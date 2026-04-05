use crate::{
    executors::{
        DURATION_BETWEEN_METRICS_REPORT, EarlyExit, EvmError, Executor, FuzzTestTimer,
        RawCallResult,
        corpus::{GlobalCorpusMetrics, WorkerCorpus},
    },
    inspectors::Fuzzer,
};
use alloy_json_abi::Function;
use alloy_primitives::{
    Address, Bytes, FixedBytes, I256, Selector, U256, keccak256,
    map::{AddressMap, HashMap},
};
use alloy_sol_types::{SolCall, sol};
use eyre::{ContextCompat, Result, eyre};
use foundry_common::{
    TestFunctionExt,
    contracts::{ContractsByAddress, ContractsByArtifact},
    sh_println,
};
use foundry_config::InvariantConfig;
use foundry_evm_core::{
    constants::{
        CALLER, CHEATCODE_ADDRESS, DEFAULT_CREATE2_DEPLOYER, HARDHAT_CONSOLE_ADDRESS, MAGIC_ASSUME,
    },
    precompiles::PRECOMPILES,
};
use foundry_evm_fuzz::{
    BasicTxDetails, FuzzCase, FuzzFixtures, FuzzedCases,
    invariant::{
        ArtifactFilters, FuzzRunIdentifiedContracts, InvariantContract, RandomCallGenerator,
        SenderFilters, TargetedContract, TargetedContracts,
    },
    strategies::{EvmFuzzState, invariant_strat, override_call_strat},
};
use foundry_evm_traces::{CallTraceArena, SparsedTraceArena};
use indicatif::ProgressBar;
use parking_lot::{Mutex, RwLock};
use proptest::{
    strategy::Strategy,
    test_runner::{RngAlgorithm, TestRng, TestRunner},
};
use rayon::iter::{IntoParallelIterator, ParallelIterator};
use result::{assert_after_invariant, can_continue, invariant_preflight_check};
use revm::state::Account;
use serde::{Deserialize, Serialize};
use serde_json::json;
use std::{
    collections::{HashMap as Map, btree_map::Entry},
    sync::{
        Arc,
        atomic::{AtomicU32, AtomicUsize, Ordering},
    },
    time::{Instant, SystemTime, UNIX_EPOCH},
};

mod error;
pub use error::{InvariantFailures, InvariantFuzzError};
use foundry_evm_coverage::HitMaps;

mod replay;
pub use replay::{generate_counterexample, replay_error, replay_run};

mod result;
pub use result::InvariantFuzzTestResult;

mod shrink;
pub use shrink::check_sequence;

sol! {
    interface IInvariantTest {
        #[derive(Default)]
        struct FuzzSelector {
            address addr;
            bytes4[] selectors;
        }

        #[derive(Default)]
        struct FuzzArtifactSelector {
            string artifact;
            bytes4[] selectors;
        }

        #[derive(Default)]
        struct FuzzInterface {
            address addr;
            string[] artifacts;
        }

        function afterInvariant() external;

        #[derive(Default)]
        function excludeArtifacts() public view returns (string[] memory excludedArtifacts);

        #[derive(Default)]
        function excludeContracts() public view returns (address[] memory excludedContracts);

        #[derive(Default)]
        function excludeSelectors() public view returns (FuzzSelector[] memory excludedSelectors);

        #[derive(Default)]
        function excludeSenders() public view returns (address[] memory excludedSenders);

        #[derive(Default)]
        function targetArtifacts() public view returns (string[] memory targetedArtifacts);

        #[derive(Default)]
        function targetArtifactSelectors() public view returns (FuzzArtifactSelector[] memory targetedArtifactSelectors);

        #[derive(Default)]
        function targetContracts() public view returns (address[] memory targetedContracts);

        #[derive(Default)]
        function targetSelectors() public view returns (FuzzSelector[] memory targetedSelectors);

        #[derive(Default)]
        function targetSenders() public view returns (address[] memory targetedSenders);

        #[derive(Default)]
        function targetInterfaces() public view returns (FuzzInterface[] memory targetedInterfaces);
    }
}

/// Contains invariant metrics for a single entry (fuzzed selector or invariant function).
#[derive(Default, Debug, Clone, Deserialize, Serialize, PartialEq, Eq)]
pub struct InvariantMetrics {
    // Count of fuzzed selector calls.
    pub calls: usize,
    // Count of fuzzed selector reverts.
    pub reverts: usize,
    // Count of fuzzed selector discards (through assume cheatcodes).
    pub discards: usize,
    // Count of times this metric entry observed a broken invariant.
    #[serde(default)]
    pub failed: usize,
}

/// Corpus syncs across workers every `SYNC_INTERVAL` runs.
const SYNC_INTERVAL: u32 = 1000;
/// Minimum number of invariant runs per worker.
const MIN_RUNS_PER_WORKER: u32 = 4;

/// Aggregated data produced by a single invariant worker.
#[derive(Default)]
struct InvariantWorkerResult {
    id: usize,
    failures: InvariantFailures,
    cases: Vec<FuzzedCases>,
    last_run_inputs: Vec<BasicTxDetails>,
    gas_report_traces: Vec<Vec<CallTraceArena>>,
    line_coverage: Option<HitMaps>,
    metrics: Map<String, InvariantMetrics>,
    optimization_best_value: Option<I256>,
    optimization_best_sequence: Vec<BasicTxDetails>,
    failed_corpus_replays: usize,
    last_run_timestamp: u128,
}

/// Shared campaign state for coordinating parallel invariant workers.
struct SharedInvariantState {
    next_run: Arc<AtomicU32>,
    timer: FuzzTestTimer,
    global_early_exit: EarlyExit,
    local_early_exit: EarlyExit,
    global_corpus_metrics: GlobalCorpusMetrics,
    global_failures: Arc<Mutex<Map<String, InvariantFuzzError>>>,
    unique_failures: Arc<AtomicUsize>,
}

impl SharedInvariantState {
    fn new(timeout: Option<u32>, early_exit: EarlyExit) -> Self {
        Self {
            next_run: Arc::new(AtomicU32::new(0)),
            timer: FuzzTestTimer::new(timeout),
            global_early_exit: early_exit,
            local_early_exit: EarlyExit::new(true),
            global_corpus_metrics: GlobalCorpusMetrics::default(),
            global_failures: Arc::new(Mutex::new(Map::default())),
            unique_failures: Arc::new(AtomicUsize::new(0)),
        }
    }

    fn should_continue(&self) -> bool {
        !(self.global_early_exit.should_stop()
            || self.local_early_exit.should_stop()
            || self.timer.is_timed_out())
    }

    /// Claims a run index for a worker, or returns `None` if the campaign is done.
    fn claim_run(&self, max_runs: u32) -> Option<u32> {
        loop {
            if !self.should_continue() {
                return None;
            }

            let current = self.next_run.load(Ordering::Relaxed);
            if current >= max_runs {
                return None;
            }

            if self
                .next_run
                .compare_exchange_weak(current, current + 1, Ordering::Relaxed, Ordering::Relaxed)
                .is_ok()
            {
                return Some(current + 1);
            }
        }
    }

    fn record_terminal_failure(&self) {
        self.local_early_exit.record_failure();
    }

    fn record_unique_failure(&self, total_invariants: usize) {
        let count = self.unique_failures.fetch_add(1, Ordering::Relaxed) + 1;
        if count >= total_invariants {
            self.local_early_exit.record_failure();
        }
    }
}

/// Contains data collected during invariant test runs.
struct InvariantTestData {
    // Consumed gas and calldata of every successful fuzz call.
    fuzz_cases: Vec<FuzzedCases>,
    // Data related to reverts or failed assertions of the test.
    failures: InvariantFailures,
    // Calldata in the last invariant run.
    last_run_inputs: Vec<BasicTxDetails>,
    // Additional traces for gas report.
    gas_report_traces: Vec<Vec<CallTraceArena>>,
    // Line coverage information collected from all fuzzed calls.
    line_coverage: Option<HitMaps>,
    // Metrics for each fuzzed selector.
    metrics: Map<String, InvariantMetrics>,

    // Proptest runner to query for random values.
    // The strategy only comes with the first `input`. We fill the rest of the `inputs`
    // until the desired `depth` so we can use the evolving fuzz dictionary
    // during the run.
    branch_runner: TestRunner,

    // Optimization mode state: tracks the best (maximum) value and the sequence that produced it.
    // Only used when invariant function returns int256.
    optimization_best_value: Option<I256>,
    optimization_best_sequence: Vec<BasicTxDetails>,
}

/// Contains invariant test data.
struct InvariantTest {
    // Fuzz state of invariant test.
    fuzz_state: EvmFuzzState,
    // Contracts fuzzed by the invariant test.
    targeted_contracts: FuzzRunIdentifiedContracts,
    // Data collected during invariant runs.
    test_data: InvariantTestData,
}

impl InvariantTest {
    /// Instantiates an invariant test.
    fn new(
        fuzz_state: EvmFuzzState,
        targeted_contracts: FuzzRunIdentifiedContracts,
        failures: InvariantFailures,
        branch_runner: TestRunner,
    ) -> Self {
        let test_data = InvariantTestData {
            fuzz_cases: vec![],
            failures,
            last_run_inputs: vec![],
            gas_report_traces: vec![],
            line_coverage: None,
            metrics: Map::default(),
            branch_runner,
            optimization_best_value: None,
            optimization_best_sequence: vec![],
        };
        Self { fuzz_state, targeted_contracts, test_data }
    }

    /// Returns number of invariant test reverts.
    fn reverts(&self) -> usize {
        self.test_data.failures.reverts
    }

    /// Whether invariant test has errors or not.
    fn has_errors(&self, invariant: &Function) -> bool {
        self.test_data.failures.has_failure(invariant)
    }

    /// Set invariant test error.
    fn set_error(&mut self, invariant: &Function, error: InvariantFuzzError) {
        self.test_data.failures.record_failure(invariant, error);
    }

    /// Set last invariant run call sequence.
    fn set_last_run_inputs(&mut self, inputs: &Vec<BasicTxDetails>) {
        self.test_data.last_run_inputs.clone_from(inputs);
    }

    /// Merge current collected line coverage with the new coverage from last fuzzed call.
    fn merge_line_coverage(&mut self, new_coverage: Option<HitMaps>) {
        HitMaps::merge_opt(&mut self.test_data.line_coverage, new_coverage);
    }

    /// Update metrics for a fuzzed selector, extracted from tx details.
    /// Always increments number of calls; discarded runs (through assume cheatcodes) are tracked
    /// separated from reverts.
    fn record_metrics(&mut self, tx_details: &BasicTxDetails, reverted: bool, discarded: bool) {
        if let Some(metric_key) =
            self.targeted_contracts.targets.lock().fuzzed_metric_key(tx_details)
        {
            let test_metrics = &mut self.test_data.metrics;
            let invariant_metrics = test_metrics.entry(metric_key).or_default();
            invariant_metrics.calls += 1;
            if discarded {
                invariant_metrics.discards += 1;
            } else if reverted {
                invariant_metrics.reverts += 1;
            }
        }
    }

    /// End invariant test run by collecting results, cleaning collected artifacts and reverting
    /// created fuzz state.
    fn end_run(&mut self, run: InvariantTestRun, gas_samples: usize) {
        // We clear all the targeted contracts created during this run.
        self.targeted_contracts.clear_created_contracts(run.created_contracts);

        if self.test_data.gas_report_traces.len() < gas_samples {
            self.test_data
                .gas_report_traces
                .push(run.run_traces.into_iter().map(|arena| arena.arena).collect());
        }
        self.test_data.fuzz_cases.push(FuzzedCases::new(run.fuzz_runs));

        // Revert state to not persist values between runs.
        self.fuzz_state.revert();
    }
}

/// Contains data for an invariant test run.
struct InvariantTestRun {
    // Invariant run call sequence.
    inputs: Vec<BasicTxDetails>,
    // Current invariant run executor.
    executor: Executor,
    // Invariant run stat reports (eg. gas usage).
    fuzz_runs: Vec<FuzzCase>,
    // Contracts created during current invariant run.
    created_contracts: Vec<Address>,
    // Traces of each call of the invariant run call sequence.
    run_traces: Vec<SparsedTraceArena>,
    // Current depth of invariant run.
    depth: u32,
    // Current assume rejects of the invariant run.
    rejects: u32,
    // Whether new coverage was discovered during this run.
    new_coverage: bool,
}

impl InvariantTestRun {
    /// Instantiates an invariant test run.
    fn new(first_input: BasicTxDetails, executor: Executor, depth: usize) -> Self {
        Self {
            inputs: vec![first_input],
            executor,
            fuzz_runs: Vec::with_capacity(depth),
            created_contracts: vec![],
            run_traces: vec![],
            depth: 0,
            rejects: 0,
            new_coverage: false,
        }
    }
}

struct InvariantWorkerSetup {
    id: usize,
    invariant_test: InvariantTest,
    corpus_manager: WorkerCorpus,
    executor: Executor,
}

struct PreparedInvariantCampaign {
    fuzz_state: EvmFuzzState,
    targeted_senders: SenderFilters,
    targeted_contracts: FuzzRunIdentifiedContracts,
    failures: InvariantFailures,
}

/// Wrapper around any [`Executor`] implementer which provides fuzzing support using [`proptest`].
///
/// After instantiation, calling `invariant_fuzz` will proceed to hammer the deployed smart
/// contracts with inputs, until it finds a counterexample sequence. The provided [`TestRunner`]
/// contains all the configuration which can be overridden via [environment
/// variables](proptest::test_runner::Config)
pub struct InvariantExecutor<'a> {
    pub executor: Executor,
    /// Proptest runner.
    runner: TestRunner,
    /// Optional base seed for deterministic invariant runs.
    seed: Option<U256>,
    /// The invariant configuration
    config: InvariantConfig,
    /// Number of parallel workers for this campaign.
    num_workers: usize,
    /// Contracts deployed with `setUp()`
    setup_contracts: &'a ContractsByAddress,
    /// Contracts that are part of the project but have not been deployed yet. We need the bytecode
    /// to identify them from the stateset changes.
    project_contracts: &'a ContractsByArtifact,
    /// Filters contracts to be fuzzed through their artifact identifiers.
    artifact_filters: ArtifactFilters,
}

impl<'a> InvariantExecutor<'a> {
    /// Instantiates a fuzzed executor EVM given a testrunner
    pub fn new(
        executor: Executor,
        runner: TestRunner,
        seed: Option<U256>,
        config: InvariantConfig,
        setup_contracts: &'a ContractsByAddress,
        project_contracts: &'a ContractsByArtifact,
    ) -> Self {
        let max_workers = Ord::max(1, config.runs / MIN_RUNS_PER_WORKER) as usize;
        let mut num_workers = Ord::min(rayon::current_num_threads(), max_workers);
        // `call_override` keeps mutable per-run state in the inspector and is not worker-safe.
        if config.call_override {
            num_workers = 1;
        }

        Self {
            executor,
            runner,
            seed,
            config,
            num_workers,
            setup_contracts,
            project_contracts,
            artifact_filters: ArtifactFilters::default(),
        }
    }

    pub fn config(self) -> InvariantConfig {
        self.config
    }

    /// Fuzzes any deployed contract and checks any broken invariant at `invariant_address`.
    pub fn invariant_fuzz(
        &mut self,
        invariant_contract: InvariantContract<'_>,
        fuzz_fixtures: &FuzzFixtures,
        fuzz_state: EvmFuzzState,
        progress: Option<&ProgressBar>,
        early_exit: &EarlyExit,
    ) -> Result<InvariantFuzzTestResult> {
        // Throw an error to abort test run if the invariant function accepts input params
        if !invariant_contract.invariant_fn.inputs.is_empty() {
            return Err(eyre!("Invariant test function should have no inputs"));
        }

        let prepared = self.prepare_test(&invariant_contract, fuzz_fixtures, fuzz_state)?;
        let edge_coverage_enabled = self.config.corpus.collect_edge_coverage();
        let shared_state = SharedInvariantState::new(self.config.timeout, early_exit.clone());

        debug!(n = self.num_workers, "spawning invariant workers");
        let worker_results = (0..self.num_workers)
            .into_par_iter()
            .map(|id| {
                let setup = self.prepare_worker(id, &prepared, fuzz_fixtures)?;
                let _guard = info_span!("invariant_worker", id = setup.id).entered();
                self.run_worker(
                    setup,
                    &invariant_contract,
                    progress,
                    edge_coverage_enabled,
                    &shared_state,
                )
            })
            .collect::<Result<Vec<_>>>()?;

        Ok(self.aggregate_worker_results(invariant_contract, worker_results, &shared_state))
    }

    fn run_worker(
        &self,
        mut setup: InvariantWorkerSetup,
        invariant_contract: &InvariantContract<'_>,
        progress: Option<&ProgressBar>,
        edge_coverage_enabled: bool,
        shared_state: &SharedInvariantState,
    ) -> Result<InvariantWorkerResult> {
        let worker_id = setup.id;
        let mut last_metrics_report = Instant::now();
        let mut runs_since_sync = SYNC_INTERVAL + worker_id as u32 * 100;
        let sync_threshold = SYNC_INTERVAL + worker_id as u32 * 100;
        let mut last_run_timestamp = 0u128;

        'campaign: while let Some(_run_idx) = shared_state.claim_run(self.config.runs) {
            runs_since_sync += 1;
            if runs_since_sync >= sync_threshold {
                let timer = Instant::now();
                setup.corpus_manager.sync(
                    self.num_workers,
                    &setup.executor,
                    None,
                    Some(&setup.invariant_test.targeted_contracts),
                    &shared_state.global_corpus_metrics,
                )?;
                trace!("finished corpus sync in {:?}", timer.elapsed());
                runs_since_sync = 0;
            }

            let initial_seq = setup.corpus_manager.new_inputs(
                &mut setup.invariant_test.test_data.branch_runner,
                &setup.invariant_test.fuzz_state,
                &setup.invariant_test.targeted_contracts,
            )?;

            let mut current_run = InvariantTestRun::new(
                initial_seq[0].clone(),
                setup.executor.clone(),
                self.config.depth as usize,
            );

            if self.config.fail_on_revert && setup.invariant_test.reverts() > 0 {
                return Err(eyre!("call reverted"));
            }

            while current_run.depth < self.config.depth {
                if shared_state.timer.is_timed_out() {
                    break 'campaign;
                }
                if !shared_state.should_continue() {
                    break 'campaign;
                }

                let tx = current_run
                    .inputs
                    .last()
                    .ok_or_else(|| eyre!("no input generated to call fuzzed target."))?;

                let mut call_result = execute_tx(&mut current_run.executor, tx)?;
                let discarded = call_result.result.as_ref() == MAGIC_ASSUME;
                if self.config.show_metrics {
                    setup.invariant_test.record_metrics(tx, call_result.reverted, discarded);
                }

                setup.invariant_test.merge_line_coverage(call_result.line_coverage.clone());
                if setup.corpus_manager.merge_edge_coverage(&mut call_result) {
                    current_run.new_coverage = true;
                }

                if discarded {
                    current_run.inputs.pop();
                    current_run.rejects += 1;
                    if current_run.rejects > self.config.max_assume_rejects {
                        setup.invariant_test.set_error(
                            invariant_contract.invariant_fn,
                            InvariantFuzzError::MaxAssumeRejects(self.config.max_assume_rejects),
                        );
                        self.merge_worker_failures(
                            &setup.invariant_test.test_data.failures,
                            invariant_contract.invariant_fns.len(),
                            shared_state,
                        );
                        shared_state.record_terminal_failure();
                        break 'campaign;
                    }
                } else {
                    current_run.executor.commit(&mut call_result);
                    let mut state_changeset = std::mem::take(&mut call_result.state_changeset);
                    if !call_result.reverted {
                        collect_data(
                            &setup.invariant_test,
                            &mut state_changeset,
                            tx,
                            &call_result,
                            self.config.depth,
                        );
                    }

                    if let Err(error) =
                        &setup.invariant_test.targeted_contracts.collect_created_contracts(
                            &state_changeset,
                            self.project_contracts,
                            self.setup_contracts,
                            &self.artifact_filters,
                            &mut current_run.created_contracts,
                        )
                    {
                        warn!(target: "forge::test", "{error}");
                    }

                    current_run
                        .fuzz_runs
                        .push(FuzzCase { gas: call_result.gas_used, stipend: call_result.stipend });

                    let can_continue = can_continue(
                        invariant_contract,
                        &mut setup.invariant_test,
                        &mut current_run,
                        &self.config,
                        call_result,
                        &state_changeset,
                    )
                    .map_err(|e| eyre!(e.to_string()))?;

                    self.merge_worker_failures(
                        &setup.invariant_test.test_data.failures,
                        invariant_contract.invariant_fns.len(),
                        shared_state,
                    );

                    if !can_continue || current_run.depth == self.config.depth - 1 {
                        setup.invariant_test.set_last_run_inputs(&current_run.inputs);
                    }
                    if !can_continue {
                        shared_state.record_terminal_failure();
                        break 'campaign;
                    }
                    current_run.depth += 1;
                }

                current_run.inputs.push(setup.corpus_manager.generate_next_input(
                    &mut setup.invariant_test.test_data.branch_runner,
                    &initial_seq,
                    discarded,
                    current_run.depth as usize,
                )?);
            }

            setup.corpus_manager.process_inputs(&current_run.inputs, current_run.new_coverage);

            if invariant_contract.call_after_invariant
                && !setup.invariant_test.has_errors(invariant_contract.invariant_fn)
            {
                assert_after_invariant(
                    invariant_contract,
                    &mut setup.invariant_test,
                    &current_run,
                    &self.config,
                )
                .map_err(|_| eyre!("Failed to call afterInvariant"))?;

                self.merge_worker_failures(
                    &setup.invariant_test.test_data.failures,
                    invariant_contract.invariant_fns.len(),
                    shared_state,
                );
            }

            setup.invariant_test.end_run(current_run, self.config.gas_report_samples as usize);
            last_run_timestamp = SystemTime::now().duration_since(UNIX_EPOCH)?.as_millis();

            if let Some(progress) = progress {
                progress.inc(1);
                if worker_id == 0 {
                    let failures = shared_state.global_failures.lock().len();
                    let mut parts = Vec::new();
                    if failures > 0 {
                        parts.push(format!("\n      ❌ Failures: {failures}\n"));
                    }
                    if edge_coverage_enabled {
                        setup.corpus_manager.sync_metrics(&shared_state.global_corpus_metrics);
                        parts.push(format!("{}", shared_state.global_corpus_metrics.load()));
                    }
                    progress.set_message(parts.join(""));
                }
            } else if edge_coverage_enabled
                && worker_id == 0
                && last_metrics_report.elapsed() > DURATION_BETWEEN_METRICS_REPORT
            {
                setup.corpus_manager.sync_metrics(&shared_state.global_corpus_metrics);
                let failed = shared_state
                    .global_failures
                    .lock()
                    .contains_key(&invariant_contract.invariant_fn.name)
                    as usize;
                let metrics = json!({
                    "timestamp": SystemTime::now()
                        .duration_since(UNIX_EPOCH)?
                        .as_secs(),
                    "invariant": invariant_contract.invariant_fn.name,
                    "failed": failed,
                    "metrics": shared_state.global_corpus_metrics.load(),
                });
                let _ = sh_println!("{}", serde_json::to_string(&metrics)?);
                last_metrics_report = Instant::now();
            }
        }

        setup.invariant_test.fuzz_state.log_stats();
        let result = setup.invariant_test.test_data;

        Ok(InvariantWorkerResult {
            id: worker_id,
            failures: result.failures,
            cases: result.fuzz_cases,
            last_run_inputs: result.last_run_inputs,
            gas_report_traces: result.gas_report_traces,
            line_coverage: result.line_coverage,
            metrics: result.metrics,
            optimization_best_value: result.optimization_best_value,
            optimization_best_sequence: result.optimization_best_sequence,
            failed_corpus_replays: if worker_id == 0 {
                setup.corpus_manager.failed_replays
            } else {
                0
            },
            last_run_timestamp,
        })
    }

    fn merge_worker_failures(
        &self,
        failures: &InvariantFailures,
        total_invariants: usize,
        shared_state: &SharedInvariantState,
    ) {
        if failures.errors.is_empty() {
            return;
        }

        let mut newly_recorded = 0;
        {
            let mut global_failures = shared_state.global_failures.lock();
            for (name, error) in &failures.errors {
                if !global_failures.contains_key(name) {
                    global_failures.insert(name.clone(), error.clone());
                    newly_recorded += 1;
                }
            }
        }

        for _ in 0..newly_recorded {
            shared_state.record_unique_failure(total_invariants);
        }
    }

    fn aggregate_worker_results(
        &self,
        invariant_contract: InvariantContract<'_>,
        workers: Vec<InvariantWorkerResult>,
        shared_state: &SharedInvariantState,
    ) -> InvariantFuzzTestResult {
        let mut errors = shared_state.global_failures.lock().clone();
        let mut cases = Vec::new();
        let mut reverts = 0usize;
        let mut last_run_inputs = Vec::new();
        let mut last_run_ts = 0u128;
        let mut gas_report_traces = Vec::new();
        let mut line_coverage = None;
        let mut metrics: Map<String, InvariantMetrics> = Map::default();
        let mut failed_corpus_replays = 0usize;
        let mut optimization_best_value: Option<I256> = None;
        let mut optimization_best_sequence = Vec::new();

        for worker in workers {
            if worker.id == 0 {
                failed_corpus_replays = worker.failed_corpus_replays;
            }
            if worker.last_run_timestamp >= last_run_ts {
                last_run_ts = worker.last_run_timestamp;
                last_run_inputs = worker.last_run_inputs.clone();
            }
            for (name, error) in &worker.failures.errors {
                errors.entry(name.clone()).or_insert_with(|| error.clone());
            }
            reverts += worker.failures.reverts;
            cases.extend(worker.cases);
            gas_report_traces.extend(worker.gas_report_traces);
            HitMaps::merge_opt(&mut line_coverage, worker.line_coverage);

            for (key, worker_metric) in worker.metrics {
                let entry = metrics.entry(key).or_default();
                entry.calls += worker_metric.calls;
                entry.reverts += worker_metric.reverts;
                entry.discards += worker_metric.discards;
                entry.failed += worker_metric.failed;
            }

            if let Some(best_value) = worker.optimization_best_value
                && optimization_best_value.is_none_or(|current| best_value > current)
            {
                optimization_best_value = Some(best_value);
                optimization_best_sequence = worker.optimization_best_sequence;
            }
        }

        if self.config.show_metrics {
            for invariant_name in errors.keys() {
                let metric_key = format!("{}.{}", invariant_contract.identifier, invariant_name);
                metrics.entry(metric_key).or_default().failed += 1;
            }
        }

        let max_gas_samples = self.config.gas_report_samples as usize;
        if gas_report_traces.len() > max_gas_samples {
            gas_report_traces.truncate(max_gas_samples);
        }

        InvariantFuzzTestResult {
            errors,
            cases,
            reverts,
            last_run_inputs,
            gas_report_traces,
            line_coverage,
            metrics,
            failed_corpus_replays,
            optimization_best_value,
            optimization_best_sequence,
        }
    }

    fn prepare_worker(
        &self,
        worker_id: usize,
        prepared: &PreparedInvariantCampaign,
        fuzz_fixtures: &FuzzFixtures,
    ) -> Result<InvariantWorkerSetup> {
        let (fuzz_state, targeted_contracts) = if self.num_workers == 1 && worker_id == 0 {
            (prepared.fuzz_state.clone(), prepared.targeted_contracts.clone())
        } else {
            (prepared.fuzz_state.fork(), prepared.targeted_contracts.fork())
        };
        let strategy = invariant_strat(
            fuzz_state.clone(),
            prepared.targeted_senders.clone(),
            targeted_contracts.clone(),
            self.config.clone(),
            fuzz_fixtures.clone(),
        )
        .no_shrink();

        let mut executor = self.executor.clone();
        if let Some(fuzzer) = executor.inspector_mut().fuzzer.as_mut() {
            fuzzer.fuzz_state = fuzz_state.clone();
        }
        let corpus_manager = WorkerCorpus::new(
            worker_id,
            self.config.corpus.clone(),
            strategy.boxed(),
            if worker_id == 0 { Some(&executor) } else { None },
            None,
            Some(&targeted_contracts),
        )?;

        let invariant_test = InvariantTest::new(
            fuzz_state,
            targeted_contracts,
            prepared.failures.clone(),
            self.worker_runner(worker_id),
        );

        Ok(InvariantWorkerSetup { id: worker_id, invariant_test, corpus_manager, executor })
    }

    fn worker_runner(&self, worker_id: usize) -> TestRunner {
        let mut runner_config = self.runner.config().clone();
        // We distribute runs manually through [`SharedInvariantState::claim_run`].
        runner_config.cases = self.config.runs.max(1);

        if let Some(seed) = self.seed {
            let worker_seed = if worker_id == 0 {
                seed
            } else {
                let seed_data =
                    [&seed.to_be_bytes::<32>()[..], &worker_id.to_be_bytes()[..]].concat();
                U256::from_be_bytes(keccak256(seed_data).0)
            };
            trace!(target: "forge::test", ?worker_seed, "deterministic seed for invariant worker {worker_id}");
            let rng = TestRng::from_seed(RngAlgorithm::ChaCha, &worker_seed.to_be_bytes::<32>());
            TestRunner::new_with_rng(runner_config, rng)
        } else {
            TestRunner::new(runner_config)
        }
    }

    /// Prepares shared campaign structures needed for all invariant workers.
    fn prepare_test(
        &mut self,
        invariant_contract: &InvariantContract<'_>,
        fuzz_fixtures: &FuzzFixtures,
        fuzz_state: EvmFuzzState,
    ) -> Result<PreparedInvariantCampaign> {
        // Finds out the chosen deployed contracts and/or senders.
        self.select_contract_artifacts(invariant_contract.address)?;
        let (targeted_senders, targeted_contracts) =
            self.select_contracts_and_senders(invariant_contract.address)?;

        // If any of the targeted contracts have the storage layout enabled then we can sample
        // mapping values. To accomplish, we need to record the mapping storage slots and keys.
        let fuzz_state =
            if targeted_contracts.targets.lock().iter().any(|(_, t)| t.storage_layout.is_some()) {
                fuzz_state.with_mapping_slots(AddressMap::default())
            } else {
                fuzz_state
            };

        // Set up fuzzer WITHOUT call_generator initially.
        // We defer call_override until after the initial invariant check to avoid
        // injecting random calls during setup which would break the invariant assertion.
        self.executor.inspector_mut().set_fuzzer(Fuzzer {
            call_generator: None,
            fuzz_state: fuzz_state.clone(),
            collect: true,
        });

        // Let's make sure the invariant is sound before actually starting the run:
        // We'll assert the invariant in its initial state, and if it fails, we'll
        // already know if we can early exit the invariant run.
        // This does not count as a fuzz run. It will just register the revert.
        let mut failures = InvariantFailures::new();
        invariant_preflight_check(
            invariant_contract,
            &self.config,
            &targeted_contracts,
            &self.executor,
            &[],
            &mut failures,
        )?;
        if let Some(error) = failures.get_failure(invariant_contract.invariant_fn) {
            return Err(eyre!(error.revert_reason().unwrap_or_default()));
        }

        // NOW enable call_override after the initial invariant check has passed.
        // This allows `override_call_strat` to inject calls during actual fuzz runs
        // for reentrancy vulnerability detection.
        if self.config.call_override {
            let target_contract_ref = Arc::new(RwLock::new(Address::ZERO));

            // Collect handler addresses - these are the contracts we want to inject
            // reentrancy into (simulating malicious receive() functions).
            let handler_addresses: std::collections::HashSet<Address> =
                targeted_contracts.targets.lock().keys().copied().collect();

            let call_generator = RandomCallGenerator::new(
                invariant_contract.address,
                handler_addresses,
                self.runner.clone(),
                override_call_strat(
                    fuzz_state.clone(),
                    targeted_contracts.clone(),
                    target_contract_ref.clone(),
                    fuzz_fixtures.clone(),
                ),
                target_contract_ref,
            );

            if let Some(fuzzer) = self.executor.inspector_mut().fuzzer.as_mut() {
                fuzzer.call_generator = Some(call_generator);
            }
        }

        Ok(PreparedInvariantCampaign { fuzz_state, targeted_senders, targeted_contracts, failures })
    }

    /// Fills the `InvariantExecutor` with the artifact identifier filters (in `path:name` string
    /// format). They will be used to filter contracts after the `setUp`, and more importantly,
    /// during the runs.
    ///
    /// Also excludes any contract without any mutable functions.
    ///
    /// Priority:
    ///
    /// targetArtifactSelectors > excludeArtifacts > targetArtifacts
    pub fn select_contract_artifacts(&mut self, invariant_address: Address) -> Result<()> {
        let targeted_artifact_selectors = self
            .executor
            .call_sol_default(invariant_address, &IInvariantTest::targetArtifactSelectorsCall {});

        // Insert them into the executor `targeted_abi`.
        for IInvariantTest::FuzzArtifactSelector { artifact, selectors } in
            targeted_artifact_selectors
        {
            let identifier = self.validate_selected_contract(artifact, &selectors)?;
            self.artifact_filters.targeted.entry(identifier).or_default().extend(selectors);
        }

        let targeted_artifacts = self
            .executor
            .call_sol_default(invariant_address, &IInvariantTest::targetArtifactsCall {});
        let excluded_artifacts = self
            .executor
            .call_sol_default(invariant_address, &IInvariantTest::excludeArtifactsCall {});

        // Insert `excludeArtifacts` into the executor `excluded_abi`.
        for contract in excluded_artifacts {
            let identifier = self.validate_selected_contract(contract, &[])?;

            if !self.artifact_filters.excluded.contains(&identifier) {
                self.artifact_filters.excluded.push(identifier);
            }
        }

        // Exclude any artifact without mutable functions.
        for (artifact, contract) in self.project_contracts.iter() {
            if contract
                .abi
                .functions()
                .filter(|func| {
                    !matches!(
                        func.state_mutability,
                        alloy_json_abi::StateMutability::Pure
                            | alloy_json_abi::StateMutability::View
                    )
                })
                .count()
                == 0
                && !self.artifact_filters.excluded.contains(&artifact.identifier())
            {
                self.artifact_filters.excluded.push(artifact.identifier());
            }
        }

        // Insert `targetArtifacts` into the executor `targeted_abi`, if they have not been seen
        // before.
        for contract in targeted_artifacts {
            let identifier = self.validate_selected_contract(contract, &[])?;

            if !self.artifact_filters.targeted.contains_key(&identifier)
                && !self.artifact_filters.excluded.contains(&identifier)
            {
                self.artifact_filters.targeted.insert(identifier, vec![]);
            }
        }
        Ok(())
    }

    /// Makes sure that the contract exists in the project. If so, it returns its artifact
    /// identifier.
    fn validate_selected_contract(
        &mut self,
        contract: String,
        selectors: &[FixedBytes<4>],
    ) -> Result<String> {
        if let Some((artifact, contract_data)) =
            self.project_contracts.find_by_name_or_identifier(&contract)?
        {
            // Check that the selectors really exist for this contract.
            for selector in selectors {
                contract_data
                    .abi
                    .functions()
                    .find(|func| func.selector().as_slice() == selector.as_slice())
                    .wrap_err(format!("{contract} does not have the selector {selector:?}"))?;
            }

            return Ok(artifact.identifier());
        }
        eyre::bail!(
            "{contract} not found in the project. Allowed format: `contract_name` or `contract_path:contract_name`."
        );
    }

    /// Selects senders and contracts based on the contract methods `targetSenders() -> address[]`,
    /// `targetContracts() -> address[]` and `excludeContracts() -> address[]`.
    pub fn select_contracts_and_senders(
        &self,
        to: Address,
    ) -> Result<(SenderFilters, FuzzRunIdentifiedContracts)> {
        let targeted_senders =
            self.executor.call_sol_default(to, &IInvariantTest::targetSendersCall {});
        let mut excluded_senders =
            self.executor.call_sol_default(to, &IInvariantTest::excludeSendersCall {});
        // Extend with default excluded addresses - https://github.com/foundry-rs/foundry/issues/4163
        excluded_senders.extend([
            CHEATCODE_ADDRESS,
            HARDHAT_CONSOLE_ADDRESS,
            DEFAULT_CREATE2_DEPLOYER,
        ]);
        // Extend with precompiles - https://github.com/foundry-rs/foundry/issues/4287
        excluded_senders.extend(PRECOMPILES);
        let sender_filters = SenderFilters::new(targeted_senders, excluded_senders);

        let selected = self.executor.call_sol_default(to, &IInvariantTest::targetContractsCall {});
        let excluded = self.executor.call_sol_default(to, &IInvariantTest::excludeContractsCall {});

        let contracts = self
            .setup_contracts
            .iter()
            .filter(|&(addr, (identifier, _))| {
                // Include to address if explicitly set as target.
                if *addr == to && selected.contains(&to) {
                    return true;
                }

                *addr != to
                    && *addr != CHEATCODE_ADDRESS
                    && *addr != HARDHAT_CONSOLE_ADDRESS
                    && (selected.is_empty() || selected.contains(addr))
                    && (excluded.is_empty() || !excluded.contains(addr))
                    && self.artifact_filters.matches(identifier)
            })
            .map(|(addr, (identifier, abi))| {
                (
                    *addr,
                    TargetedContract::new(identifier.clone(), abi.clone())
                        .with_project_contracts(self.project_contracts),
                )
            })
            .collect();
        let mut contracts = TargetedContracts { inner: contracts };

        self.target_interfaces(to, &mut contracts)?;

        self.select_selectors(to, &mut contracts)?;

        // There should be at least one contract identified as target for fuzz runs.
        if contracts.is_empty() {
            eyre::bail!("No contracts to fuzz.");
        }

        Ok((sender_filters, FuzzRunIdentifiedContracts::new(contracts, selected.is_empty())))
    }

    /// Extends the contracts and selectors to fuzz with the addresses and ABIs specified in
    /// `targetInterfaces() -> (address, string[])[]`. Enables targeting of addresses that are
    /// not deployed during `setUp` such as when fuzzing in a forked environment. Also enables
    /// targeting of delegate proxies and contracts deployed with `create` or `create2`.
    pub fn target_interfaces(
        &self,
        invariant_address: Address,
        targeted_contracts: &mut TargetedContracts,
    ) -> Result<()> {
        let interfaces = self
            .executor
            .call_sol_default(invariant_address, &IInvariantTest::targetInterfacesCall {});

        // Since `targetInterfaces` returns a tuple array there is no guarantee
        // that the addresses are unique this map is used to merge functions of
        // the specified interfaces for the same address. For example:
        // `[(addr1, ["IERC20", "IOwnable"])]` and `[(addr1, ["IERC20"]), (addr1, ("IOwnable"))]`
        // should be equivalent.
        let mut combined = TargetedContracts::new();

        // Loop through each address and its associated artifact identifiers.
        // We're borrowing here to avoid taking full ownership.
        for IInvariantTest::FuzzInterface { addr, artifacts } in &interfaces {
            // Identifiers are specified as an array, so we loop through them.
            for identifier in artifacts {
                // Try to find the contract by name or identifier in the project's contracts.
                if let Some((_, contract_data)) =
                    self.project_contracts.iter().find(|(artifact, _)| {
                        &artifact.name == identifier || &artifact.identifier() == identifier
                    })
                {
                    let abi = &contract_data.abi;
                    combined
                        // Check if there's an entry for the given key in the 'combined' map.
                        .entry(*addr)
                        // If the entry exists, extends its ABI with the function list.
                        .and_modify(|entry| {
                            // Extend the ABI's function list with the new functions.
                            entry.abi.functions.extend(abi.functions.clone());
                        })
                        // Otherwise insert it into the map.
                        .or_insert_with(|| {
                            let mut contract =
                                TargetedContract::new(identifier.to_string(), abi.clone());
                            contract.storage_layout =
                                contract_data.storage_layout.as_ref().map(Arc::clone);
                            contract
                        });
                }
            }
        }

        targeted_contracts.extend(combined.inner);

        Ok(())
    }

    /// Selects the functions to fuzz based on the contract method `targetSelectors()` and
    /// `targetArtifactSelectors()`.
    pub fn select_selectors(
        &self,
        address: Address,
        targeted_contracts: &mut TargetedContracts,
    ) -> Result<()> {
        for (address, (identifier, _)) in self.setup_contracts {
            if let Some(selectors) = self.artifact_filters.targeted.get(identifier) {
                self.add_address_with_functions(*address, selectors, false, targeted_contracts)?;
            }
        }

        let mut target_test_selectors = vec![];
        let mut excluded_test_selectors = vec![];

        // Collect contract functions marked as target for fuzzing campaign.
        let selectors =
            self.executor.call_sol_default(address, &IInvariantTest::targetSelectorsCall {});
        for IInvariantTest::FuzzSelector { addr, selectors } in selectors {
            if addr == address {
                target_test_selectors = selectors.clone();
            }
            self.add_address_with_functions(addr, &selectors, false, targeted_contracts)?;
        }

        // Collect contract functions excluded from fuzzing campaign.
        let excluded_selectors =
            self.executor.call_sol_default(address, &IInvariantTest::excludeSelectorsCall {});
        for IInvariantTest::FuzzSelector { addr, selectors } in excluded_selectors {
            if addr == address {
                // If fuzz selector address is the test contract, then record selectors to be
                // later excluded if needed.
                excluded_test_selectors = selectors.clone();
            }
            self.add_address_with_functions(addr, &selectors, true, targeted_contracts)?;
        }

        if target_test_selectors.is_empty()
            && let Some(target) = targeted_contracts.get(&address)
        {
            // If test contract is marked as a target and no target selector explicitly set, then
            // include only state-changing functions that are not reserved and selectors that are
            // not explicitly excluded.
            let selectors: Vec<_> = target
                .abi
                .functions()
                .filter_map(|func| {
                    if matches!(
                        func.state_mutability,
                        alloy_json_abi::StateMutability::Pure
                            | alloy_json_abi::StateMutability::View
                    ) || func.is_reserved()
                        || excluded_test_selectors.contains(&func.selector())
                    {
                        None
                    } else {
                        Some(func.selector())
                    }
                })
                .collect();
            self.add_address_with_functions(address, &selectors, false, targeted_contracts)?;
        }

        Ok(())
    }

    /// Adds the address and fuzzed or excluded functions to `TargetedContracts`.
    fn add_address_with_functions(
        &self,
        address: Address,
        selectors: &[Selector],
        should_exclude: bool,
        targeted_contracts: &mut TargetedContracts,
    ) -> eyre::Result<()> {
        // Do not add address in target contracts if no function selected.
        if selectors.is_empty() {
            return Ok(());
        }

        let contract = match targeted_contracts.entry(address) {
            Entry::Occupied(entry) => entry.into_mut(),
            Entry::Vacant(entry) => {
                let (identifier, abi) = self.setup_contracts.get(&address).ok_or_else(|| {
                    eyre::eyre!(
                        "[{}] address does not have an associated contract: {}",
                        if should_exclude { "excludeSelectors" } else { "targetSelectors" },
                        address
                    )
                })?;
                entry.insert(
                    TargetedContract::new(identifier.clone(), abi.clone())
                        .with_project_contracts(self.project_contracts),
                )
            }
        };
        contract.add_selectors(selectors.iter().copied(), should_exclude)?;
        Ok(())
    }
}

/// Collects data from call for fuzzing. However, it first verifies that the sender is not an EOA
/// before inserting it into the dictionary. Otherwise, we flood the dictionary with
/// randomly generated addresses.
fn collect_data(
    invariant_test: &InvariantTest,
    state_changeset: &mut HashMap<Address, Account>,
    tx: &BasicTxDetails,
    call_result: &RawCallResult,
    run_depth: u32,
) {
    // Verify it has no code.
    let mut has_code = false;
    if let Some(Some(code)) =
        state_changeset.get(&tx.sender).map(|account| account.info.code.as_ref())
    {
        has_code = !code.is_empty();
    }

    // We keep the nonce changes to apply later.
    let mut sender_changeset = None;
    if !has_code {
        sender_changeset = state_changeset.remove(&tx.sender);
    }

    // Collect values from fuzzed call result and add them to fuzz dictionary.
    invariant_test.fuzz_state.collect_values_from_call(
        &invariant_test.targeted_contracts,
        tx,
        &call_result.result,
        &call_result.logs,
        &*state_changeset,
        run_depth,
    );

    // Re-add changes
    if let Some(changed) = sender_changeset {
        state_changeset.insert(tx.sender, changed);
    }
}

/// Calls the `afterInvariant()` function on a contract.
/// Returns call result and if call succeeded.
/// The state after the call is not persisted.
pub(crate) fn call_after_invariant_function(
    executor: &Executor,
    to: Address,
) -> Result<(RawCallResult, bool), EvmError> {
    let calldata = Bytes::from_static(&IInvariantTest::afterInvariantCall::SELECTOR);
    let mut call_result = executor.call_raw(CALLER, to, calldata, U256::ZERO)?;
    let success = executor.is_raw_call_mut_success(to, &mut call_result, false);
    Ok((call_result, success))
}

/// Calls the invariant function and returns call result and if succeeded.
pub(crate) fn call_invariant_function(
    executor: &Executor,
    address: Address,
    calldata: Bytes,
) -> Result<(RawCallResult, bool)> {
    let mut call_result = executor.call_raw(CALLER, address, calldata, U256::ZERO)?;
    let success = executor.is_raw_call_mut_success(address, &mut call_result, false);
    Ok((call_result, success))
}

/// Executes a fuzz call and returns the result.
/// Applies any block timestamp (warp) and block number (roll) adjustments before the call.
pub(crate) fn execute_tx(executor: &mut Executor, tx: &BasicTxDetails) -> Result<RawCallResult> {
    let warp = tx.warp.unwrap_or_default();
    let roll = tx.roll.unwrap_or_default();

    if warp > 0 || roll > 0 {
        // Apply pre-call block adjustments to the executor's env.
        executor.env_mut().evm_env.block_env.timestamp += warp;
        executor.env_mut().evm_env.block_env.number += roll;

        // Also update the inspector's cheatcodes.block if set.
        // The inspector's block may override the env during interpreter initialization,
        // so we need to add our warp/roll on top of any existing cheatcode-set values.
        let block_env = executor.env().evm_env.block_env.clone();
        if let Some(cheatcodes) = executor.inspector_mut().cheatcodes.as_mut() {
            if let Some(block) = cheatcodes.block.as_mut() {
                block.timestamp += warp;
                block.number += roll;
            } else {
                cheatcodes.block = Some(block_env);
            }
        }
    }

    executor
        .call_raw(tx.sender, tx.call_details.target, tx.call_details.calldata.clone(), U256::ZERO)
        .map_err(|e| eyre!(format!("Could not make raw evm call: {e}")))
}
