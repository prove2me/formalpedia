-- Prove2me | solution 1 for CountingMatroid.Analysis.RestartStageAttemptMean.restart_stage_attempt_mean
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-10-24T16:46:05.294815+00:00
-- url     : https://prove2.me/submissions/c07c8d8a-1910-4122-bdaa-f6416216edad

import Definitions.Def_CountingMatroidSupport_Computation_Charged
import Definitions.Def_CountingMatroidSupport_Computation_Charged_Extension1
import Definitions.Def_CountingMatroidSupport_Computation_Charged_Extension2
import Definitions.Def_CountingMatroidSupport_Computation_Cost
import Definitions.Def_CountingMatroidSupport_Computation_Cost_Extension1
import Definitions.Def_CountingMatroidSupport_Computation_Dict
import Definitions.Def_CountingMatroidSupport_Computation_Heap
import Definitions.Def_CountingMatroidSupport_Computation_Machine
import Definitions.Def_CountingMatroidSupport_Computation_Machine_Extension1
import Definitions.Def_CountingMatroidSupport_Computation_Num
import Definitions.Def_CountingMatroidSupport_Computation_Queue
import Definitions.Def_CountingMatroidSupport_Computation_Rand
import Definitions.Def_CountingMatroidSupport_Computation_Roster
import Definitions.Def_CountingMatroidSupport_Computation_Slot
import Definitions.Def_CountingMatroidSupport_Computation_Space
import Definitions.Def_CountingMatroidSupport_Computation_Std
import Definitions.Def_CountingMatroidSupport_MarkovChains_Chains_Metropolis
import Definitions.Def_CountingMatroidSupport_MarkovChains_Techniques_Dirichlet
import Definitions.Def_CountingMatroidSupport_MarkovChains_Techniques_HittingTime
import Definitions.Def_CountingMatroidSupport_MarkovChains_Techniques_PotentialDecay
import Definitions.Def_CountingMatroidSupport_MarkovChains_Techniques_SpectralGap
import Definitions.Def_CountingMatroidSupport_Probability_Bilinear
import Definitions.Def_CountingMatroidSupport_Probability_FinDist
import Definitions.Def_CountingMatroidSupport_Probability_FinDistFunctional
import Definitions.Def_CountingMatroid_Analysis_AnnealingPartitionDrift
import Definitions.Def_CountingMatroid_Analysis_BalancedCliqueFlow
import Definitions.Def_CountingMatroid_Analysis_BoundedRunPhase
import Definitions.Def_CountingMatroid_Analysis_BoundedRunPhaseHistory
import Definitions.Def_CountingMatroid_Analysis_BoundedRunPhaseWork
import Definitions.Def_CountingMatroid_Analysis_BoundedUniformAbortMass
import Definitions.Def_CountingMatroid_Analysis_BoundedUniformReplay
import Definitions.Def_CountingMatroid_Analysis_CappedRestartFinalTraceDomination
import Definitions.Def_CountingMatroid_Analysis_CappedReturnSubstationary
import Definitions.Def_CountingMatroid_Analysis_CappedTraceIterationSubkernel
import Definitions.Def_CountingMatroid_Analysis_CappedTraceReturnSubkernel
import Definitions.Def_CountingMatroid_Analysis_ChainDrawSiteReplay
import Definitions.Def_CountingMatroid_Analysis_ChainStepIntervalReplay
import Definitions.Def_CountingMatroid_Analysis_ConditionalDefectCoefficients
import Definitions.Def_CountingMatroid_Analysis_ConditionalDefectExtractionCoefficients
import Definitions.Def_CountingMatroid_Analysis_ConditionalDefectQuadratics
import Definitions.Def_CountingMatroid_Analysis_ConditionalSelectedStateSum
import Definitions.Def_CountingMatroid_Analysis_ConditionalTransversalSlots
import Definitions.Def_CountingMatroid_Analysis_ConditionalTransversalSplitTransport
import Definitions.Def_CountingMatroid_Analysis_ConditionalVarianceTree
import Definitions.Def_CountingMatroid_Analysis_CoveredChainIndexedSubkernel
import Definitions.Def_CountingMatroid_Analysis_CoveredChainStepSubkernel
import Definitions.Def_CountingMatroid_Analysis_CubicTensorContraction
import Definitions.Def_CountingMatroid_Analysis_DefectPartitionPositive
import Definitions.Def_CountingMatroid_Analysis_DefectPartitionQuadraticConstruction
import Definitions.Def_CountingMatroid_Analysis_DefectSlotConservation
import Definitions.Def_CountingMatroid_Analysis_DefectSlotSplitSignature
import Definitions.Def_CountingMatroid_Analysis_DisjointFlowSum
import Definitions.Def_CountingMatroid_Analysis_EmbeddedFlow
import Definitions.Def_CountingMatroid_Analysis_EmpiricalPhaseCertificate
import Definitions.Def_CountingMatroid_Analysis_EstimateMedianResource
import Definitions.Def_CountingMatroid_Analysis_ExchangeFlowEnergy
import Definitions.Def_CountingMatroid_Analysis_FinishPhaseEmpiricalUpdate
import Definitions.Def_CountingMatroid_Analysis_FinishPhaseWork
import Definitions.Def_CountingMatroid_Analysis_FiniteStoppedFiberMass
import Definitions.Def_CountingMatroid_Analysis_FirstPhaseFailure
import Definitions.Def_CountingMatroid_Analysis_IdealExchangeChain
import Definitions.Def_CountingMatroid_Analysis_InitialMultipliersGood
import Definitions.Def_CountingMatroid_Analysis_LeafCliqueFlow
import Definitions.Def_CountingMatroid_Analysis_LorentzianDirectionalSignature
import Definitions.Def_CountingMatroid_Analysis_ObservableProjection
import Definitions.Def_CountingMatroid_Analysis_ObservableVarianceDecomposition
import Definitions.Def_CountingMatroid_Analysis_ObservePhaseWork
import Definitions.Def_CountingMatroid_Analysis_OmittedRankWeightPolynomial
import Definitions.Def_CountingMatroid_Analysis_OmittedSlotCoefficientFormula
import Definitions.Def_CountingMatroid_Analysis_OmittedSlotQuadratic
import Definitions.Def_CountingMatroid_Analysis_OmittedTutteNormalization
import Definitions.Def_CountingMatroid_Analysis_PhaseChainWork
import Definitions.Def_CountingMatroid_Analysis_PhaseMeanCertificate
import Definitions.Def_CountingMatroid_Analysis_PhaseObservationExperiment
import Definitions.Def_CountingMatroid_Analysis_PhaseResourcePrimitives
import Definitions.Def_CountingMatroid_Analysis_PositiveTimeTraceChain
import Definitions.Def_CountingMatroid_Analysis_PositiveTimeTraceHarmonic
import Definitions.Def_CountingMatroid_Analysis_PositiveTimeTraceKernel
import Definitions.Def_CountingMatroid_Analysis_ProgramExchangeAcceptanceSubkernel
import Definitions.Def_CountingMatroid_Analysis_QuadraticNonpositiveHyperplane
import Definitions.Def_CountingMatroid_Analysis_RankWeightQuadraticSignature
import Definitions.Def_CountingMatroid_Analysis_RankWeightSupportExchange
import Definitions.Def_CountingMatroid_Analysis_RationalAcceptanceSubkernel
import Definitions.Def_CountingMatroid_Analysis_RationalHeight
import Definitions.Def_CountingMatroid_Analysis_RecordedObservationTrajectory
import Definitions.Def_CountingMatroid_Analysis_RecordedTraceContinuationBound
import Definitions.Def_CountingMatroid_Analysis_RelativeObservationBounds
import Definitions.Def_CountingMatroid_Analysis_RestartAttemptAccounting
import Definitions.Def_CountingMatroid_Analysis_RestartAttemptBudget
import Definitions.Def_CountingMatroid_Analysis_RestartPhaseBitCoverage
import Definitions.Def_CountingMatroid_Analysis_RestartStageAttemptMean
import Definitions.Def_CountingMatroid_Analysis_RestartStageWarmStart
import Definitions.Def_CountingMatroid_Analysis_RestartSuffixMassDefinition
import Definitions.Def_CountingMatroid_Analysis_ReturnAttemptTail
import Definitions.Def_CountingMatroid_Analysis_ScheduleConfidence
import Definitions.Def_CountingMatroid_Analysis_ScheduleDrawTrialsBridge
import Definitions.Def_CountingMatroid_Analysis_ScheduleOpeningCost
import Definitions.Def_CountingMatroid_Analysis_ScheduleThermalSetupCost
import Definitions.Def_CountingMatroid_Analysis_SelectedMetropolisKernel
import Definitions.Def_CountingMatroid_Analysis_SelectedPairedBijection
import Definitions.Def_CountingMatroid_Analysis_SlotBlockSignature
import Definitions.Def_CountingMatroid_Analysis_SlotDemandPairing
import Definitions.Def_CountingMatroid_Analysis_SlotDemandRecursion
import Definitions.Def_CountingMatroid_Analysis_SlotTransportFlow
import Definitions.Def_CountingMatroid_Analysis_SquarefreeCoordinateHessian
import Definitions.Def_CountingMatroid_Analysis_StationaryMeanIdentities
import Definitions.Def_CountingMatroid_Analysis_StationaryMeanLowerBound
import Definitions.Def_CountingMatroid_Analysis_StationaryObservableMSE
import Definitions.Def_CountingMatroid_Analysis_StationaryPathMoment
import Definitions.Def_CountingMatroid_Analysis_StationaryReturnOccupation
import Definitions.Def_CountingMatroid_Analysis_ThreePairSignatureSchur
import Definitions.Def_CountingMatroid_Analysis_TransversalClassPartition
import Definitions.Def_CountingMatroid_Analysis_TransversalEventMean
import Definitions.Def_CountingMatroid_Analysis_TransversalPartition
import Definitions.Def_CountingMatroid_Analysis_TransversalProjection
import Definitions.Def_CountingMatroid_Analysis_TransversalTraceSpectralGap
import Definitions.Def_CountingMatroid_Analysis_TwoPairSignatureBound
import Definitions.Def_CountingMatroid_Interface_Pseudocode
import Definitions.Def_CountingMatroid_Interface_Pseudocode_Extension1
import Definitions.Def_CountingMatroid_Model_Operations
import Definitions.Def_CountingMatroid_Model_Prelude
import Definitions.Def_CountingMatroid_Model_Program
import Definitions.Def_CountingMatroid_Model_Run
import Definitions.Def_CountingMatroid_Model_Subroutines
import Lean
import Mathlib.Algebra.BigOperators.Field
import Mathlib.Algebra.BigOperators.Fin
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Algebra.BigOperators.Group.Finset.Defs
import Mathlib.Algebra.BigOperators.Ring.Finset
import Mathlib.Algebra.MvPolynomial.Degrees
import Mathlib.Algebra.MvPolynomial.PDeriv
import Mathlib.Algebra.MvPolynomial.Rename
import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Mathlib.Algebra.Order.Chebyshev
import Mathlib.Algebra.Order.Field.Basic
import Mathlib.Algebra.Order.Floor.Defs
import Mathlib.Algebra.Order.Group.Int
import Mathlib.Algebra.Order.Ring.Pow
import Mathlib.Algebra.QuadraticDiscriminant
import Mathlib.Analysis.Complex.ExponentialBounds
import Mathlib.Analysis.InnerProductSpace.Spectrum
import Mathlib.Analysis.Matrix.PosDef
import Mathlib.Analysis.Matrix.Spectrum
import Mathlib.Analysis.Real.Sqrt
import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Analysis.SpecificLimits.Basic
import Mathlib.Combinatorics.Matroid.Rank.ENat
import Mathlib.Combinatorics.Matroid.Sum
import Mathlib.Data.BitVec
import Mathlib.Data.ENNReal.Inv
import Mathlib.Data.Fin.Tuple.Basic
import Mathlib.Data.Finset.Card
import Mathlib.Data.Finset.Powerset
import Mathlib.Data.Finset.Prod
import Mathlib.Data.Finsupp.Indicator
import Mathlib.Data.Finsupp.Multiset
import Mathlib.Data.Fintype.Basic
import Mathlib.Data.Fintype.BigOperators
import Mathlib.Data.Fintype.Card
import Mathlib.Data.Fintype.Powerset
import Mathlib.Data.Fintype.Vector
import Mathlib.Data.List.Basic
import Mathlib.Data.List.Induction
import Mathlib.Data.List.Infix
import Mathlib.Data.List.Nodup
import Mathlib.Data.List.OfFn
import Mathlib.Data.List.Sort
import Mathlib.Data.Multiset.Basic
import Mathlib.Data.Multiset.Count
import Mathlib.Data.Nat.Log
import Mathlib.Data.Rat.Defs
import Mathlib.Data.Real.Basic
import Mathlib.Data.Set.Card.Arithmetic
import Mathlib.Data.Set.Finite.List
import Mathlib.LinearAlgebra.Matrix.BilinearForm
import Mathlib.LinearAlgebra.QuadraticForm.Basic
import Mathlib.LinearAlgebra.QuadraticForm.Signature
import Mathlib.Order.Interval.Finset.Fin
import Mathlib.Order.Interval.Set.Basic
import Mathlib.Probability.ProbabilityMassFunction.Constructions
import Mathlib.RingTheory.MvPolynomial.EulerIdentity
import Mathlib.RingTheory.MvPolynomial.Homogeneous
import Mathlib.Tactic
import Mathlib.Tactic.Abel
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.GCongr
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Push
import Mathlib.Tactic.Ring
import Mathlib.Tactic.Ring.RingNF
import Mathlib.Topology.Algebra.Order.Field
import Mathlib.Topology.Instances.Rat
import Mathlib.Topology.Instances.Real.Lemmas
import Mathlib.Topology.Order.MonotoneConvergence
import Theorems.Thm_CountingMatroid_Analysis_CappedRestartFinalTraceDomination_restart_phase_cursor_projection
import Theorems.Thm_CountingMatroid_Analysis_CoveredChainStepSubkernel_covered_chain_step_subkernel
import Theorems.Thm_CountingMatroid_Analysis_FiniteStoppedKernelBind_stopped_kernel_bind_covered_bound
import Theorems.Thm_CountingMatroid_Analysis_RecordedTraceContinuationBound_classified_card
import Theorems.Thm_CountingMatroid_Analysis_RestartPhaseTransversal_restartPhase_transversal
import Theorems.Thm_CountingMatroid_Analysis_RestartPhaseTransversal_traceReturn_transversal
import Theorems.Thm_CountingMatroid_Analysis_RestartStageAttemptMean_layer_mass
import Theorems.Thm_CountingMatroid_Analysis_RestartStageWarmStart_history_prefix_facts
import Theorems.Thm_CountingMatroid_Analysis_RestartStageWarmStart_stage_cursor_budget
import Theorems.Thm_CountingMatroid_Analysis_RestartStageWarmStart_stage_cursor_success_interval
import Theorems.Thm_CountingMatroid_Analysis_RestartStageWarmStart_stage_warm_start
import Theorems.Thm_CountingMatroid_Analysis_ReturnAttemptTail_attempt_scan_le
import Theorems.Thm_CountingMatroid_Analysis_ReturnAttemptTail_attempt_scan_tail
import Theorems.Thm_CountingMatroid_Analysis_ReturnAttemptTail_return_occupation_eq_tail_sum

namespace Arlib.MarkovChains
end Arlib.MarkovChains
namespace Arlib.MarkovChains.FinChain
end Arlib.MarkovChains.FinChain
namespace Arlib.MarkovChains.FinKernel
end Arlib.MarkovChains.FinKernel
namespace Arlib
end Arlib
namespace Arlib.Probability
end Arlib.Probability
namespace Arlib.Probability.FinDist
end Arlib.Probability.FinDist
namespace Arlib.Probability.FinKernel
end Arlib.Probability.FinKernel
namespace CountingMatroid.Meta
end CountingMatroid.Meta
namespace CountingMatroid.Analysis.ChainStepNoninvalid
end CountingMatroid.Analysis.ChainStepNoninvalid
namespace CountingMatroid.Analysis.FiniteObservationMarkov
end CountingMatroid.Analysis.FiniteObservationMarkov
namespace CountingMatroid.Analysis.FiniteTapePrefixBound
end CountingMatroid.Analysis.FiniteTapePrefixBound
namespace CountingMatroid.Analysis.InitialRestartLaw
end CountingMatroid.Analysis.InitialRestartLaw
namespace CountingMatroid.Interface
end CountingMatroid.Interface
namespace CountingMatroid.Analysis.TransversalRankBridge
end CountingMatroid.Analysis.TransversalRankBridge
namespace CountingMatroid.Analysis.GreedyRankCorrect
end CountingMatroid.Analysis.GreedyRankCorrect
namespace CountingMatroid.Analysis.SuccessfulPrefixAbortBound
end CountingMatroid.Analysis.SuccessfulPrefixAbortBound
namespace CountingMatroid.Analysis.BoundedRunResourceEnvelope
end CountingMatroid.Analysis.BoundedRunResourceEnvelope
namespace CountingMatroid.Analysis.BoundedRunOtherSteps
end CountingMatroid.Analysis.BoundedRunOtherSteps
namespace CountingMatroid.Analysis.ScheduleOtherStepsEnvelope
end CountingMatroid.Analysis.ScheduleOtherStepsEnvelope
namespace CountingMatroid.Analysis.LeastHalvingsCost
end CountingMatroid.Analysis.LeastHalvingsCost
namespace CountingMatroid.Analysis
end CountingMatroid.Analysis
namespace CountingMatroid.Analysis.RestartPhaseWork
end CountingMatroid.Analysis.RestartPhaseWork
namespace CountingMatroid.Analysis.BoundedRunPhase
end CountingMatroid.Analysis.BoundedRunPhase
namespace CountingMatroid.Analysis.FinishPhaseWeightsSize
end CountingMatroid.Analysis.FinishPhaseWeightsSize
namespace CountingMatroid.Analysis.BoundedRunOracleCalls
end CountingMatroid.Analysis.BoundedRunOracleCalls
namespace CountingMatroid.Analysis.ResourceBound
end CountingMatroid.Analysis.ResourceBound
namespace CountingMatroid.Analysis.PhaseBitCursorBound
end CountingMatroid.Analysis.PhaseBitCursorBound
namespace CountingMatroid.Analysis.PhaseHistoryMultiplierLength
end CountingMatroid.Analysis.PhaseHistoryMultiplierLength
namespace CountingMatroid.Analysis.ChainStepBitBound
end CountingMatroid.Analysis.ChainStepBitBound
namespace CountingMatroid.Analysis.ScheduleResourceEnvelope
end CountingMatroid.Analysis.ScheduleResourceEnvelope
namespace CountingMatroid.Analysis.ScheduleCostEnvelope
end CountingMatroid.Analysis.ScheduleCostEnvelope
namespace CountingMatroid.Analysis.ScheduleValueEnvelope
end CountingMatroid.Analysis.ScheduleValueEnvelope
namespace CountingMatroid.Analysis.ScheduledTransversalTraceMixing
end CountingMatroid.Analysis.ScheduledTransversalTraceMixing
namespace CountingMatroid.Analysis.PositiveTimeTraceMixing
end CountingMatroid.Analysis.PositiveTimeTraceMixing
namespace CountingMatroid.Analysis.IdealChainNonnegDefinite
end CountingMatroid.Analysis.IdealChainNonnegDefinite
namespace CountingMatroid.Analysis.ExchangeProposalGeometry
end CountingMatroid.Analysis.ExchangeProposalGeometry
namespace CountingMatroid.Analysis.ObservablePoincare
end CountingMatroid.Analysis.ObservablePoincare
namespace CountingMatroid.Analysis.DefectMeanExchangeFlow
end CountingMatroid.Analysis.DefectMeanExchangeFlow
namespace CountingMatroid.Analysis.DefectTransportRaw
end CountingMatroid.Analysis.DefectTransportRaw
namespace CountingMatroid.Analysis.DefectLeafClassifier
end CountingMatroid.Analysis.DefectLeafClassifier
namespace CountingMatroid.Analysis.DefectSlotRoot
end CountingMatroid.Analysis.DefectSlotRoot
namespace CountingMatroid.Analysis.ConditionalLeafClassifier
end CountingMatroid.Analysis.ConditionalLeafClassifier
namespace CountingMatroid.Analysis.SlotOmissionPatternCharacterization
end CountingMatroid.Analysis.SlotOmissionPatternCharacterization
namespace CountingMatroid.Analysis.TwoLabelDerivativeNilpotence
end CountingMatroid.Analysis.TwoLabelDerivativeNilpotence
namespace CountingMatroid.Analysis.MixedDirectionalRankWeightSignature
end CountingMatroid.Analysis.MixedDirectionalRankWeightSignature
namespace CountingMatroid.Analysis.RankWeightCoordinateLorentzian
end CountingMatroid.Analysis.RankWeightCoordinateLorentzian
namespace CountingMatroid.Analysis.RankWeightCoordinateSignature
end CountingMatroid.Analysis.RankWeightCoordinateSignature
namespace CountingMatroid.Analysis.RankWeightResidualSignature
end CountingMatroid.Analysis.RankWeightResidualSignature
namespace CountingMatroid.Analysis.RankWeightClosurePair
end CountingMatroid.Analysis.RankWeightClosurePair
namespace CountingMatroid.Analysis.ClosureClassQuadraticBound
end CountingMatroid.Analysis.ClosureClassQuadraticBound
namespace CountingMatroid.Analysis.SquarefreeFullDerivative
end CountingMatroid.Analysis.SquarefreeFullDerivative
namespace CountingMatroid.Analysis.BinaryRankWeightSignature
end CountingMatroid.Analysis.BinaryRankWeightSignature
namespace CountingMatroid.Analysis.CubicDirectionalSignature
end CountingMatroid.Analysis.CubicDirectionalSignature
namespace CountingMatroid.Analysis.CubicTensorRayleighContraction
end CountingMatroid.Analysis.CubicTensorRayleighContraction
namespace CountingMatroid.Analysis.NonnegativeContractionLimit
end CountingMatroid.Analysis.NonnegativeContractionLimit
namespace CountingMatroid.Analysis.QuadraticHyperplanePointwiseLimit
end CountingMatroid.Analysis.QuadraticHyperplanePointwiseLimit
namespace CountingMatroid.Analysis.ConnectedRayleighHyperplane
end CountingMatroid.Analysis.ConnectedRayleighHyperplane
namespace CountingMatroid.Analysis.ConnectedNormalizedRayleigh
end CountingMatroid.Analysis.ConnectedNormalizedRayleigh
namespace CountingMatroid.Analysis.ConnectedLaplacianKernel
end CountingMatroid.Analysis.ConnectedLaplacianKernel
namespace CountingMatroid.Analysis.RayleighFixedKernel
end CountingMatroid.Analysis.RayleighFixedKernel
namespace CountingMatroid.Analysis.QuadraticSignatureHyperplane
end CountingMatroid.Analysis.QuadraticSignatureHyperplane
namespace CountingMatroid.Analysis.CubicExchangeCut
end CountingMatroid.Analysis.CubicExchangeCut
namespace CountingMatroid.Analysis.CubicThirdDerivativeSupport
end CountingMatroid.Analysis.CubicThirdDerivativeSupport
namespace CountingMatroid.Analysis.NonnegativeDirectionalMConvexSupport
end CountingMatroid.Analysis.NonnegativeDirectionalMConvexSupport
namespace CountingMatroid.Analysis.LinearSubstitutionHessian
end CountingMatroid.Analysis.LinearSubstitutionHessian
namespace CountingMatroid.Analysis.LinearPolynomialChainRule
end CountingMatroid.Analysis.LinearPolynomialChainRule
namespace CountingMatroid.Analysis.PairedRankValue
end CountingMatroid.Analysis.PairedRankValue
namespace CountingMatroid.Analysis.SignatureOrthogonalNonpositive
end CountingMatroid.Analysis.SignatureOrthogonalNonpositive
namespace CountingMatroid.Analysis.TypeMassLowerBounds
end CountingMatroid.Analysis.TypeMassLowerBounds
namespace CountingMatroid.Analysis.SlotLeafGeometry
end CountingMatroid.Analysis.SlotLeafGeometry
namespace CountingMatroid.Analysis.LeafExchangeProposal
end CountingMatroid.Analysis.LeafExchangeProposal
namespace CountingMatroid.Analysis.BalancedCliqueEnergy
end CountingMatroid.Analysis.BalancedCliqueEnergy
namespace CountingMatroid.Analysis.OnePairObservablePoincare
end CountingMatroid.Analysis.OnePairObservablePoincare
namespace CountingMatroid.Analysis.DefectSlotBudget
end CountingMatroid.Analysis.DefectSlotBudget
namespace CountingMatroid.Analysis.DefectSlotFutureBound
end CountingMatroid.Analysis.DefectSlotFutureBound
namespace CountingMatroid.Analysis.DefectTransportTwoPairs
end CountingMatroid.Analysis.DefectTransportTwoPairs
namespace CountingMatroid.Analysis.DefectPartitionTriangle
end CountingMatroid.Analysis.DefectPartitionTriangle
namespace CountingMatroid.Analysis.DefectPartitionQuadraticExtraction
end CountingMatroid.Analysis.DefectPartitionQuadraticExtraction
namespace CountingMatroid.Analysis.ConditionalOperationalCoefficients
end CountingMatroid.Analysis.ConditionalOperationalCoefficients
namespace CountingMatroid.Analysis.ConditionalOccupancyCoefficients
end CountingMatroid.Analysis.ConditionalOccupancyCoefficients
namespace CountingMatroid.Analysis.TransversalVarianceBound
end CountingMatroid.Analysis.TransversalVarianceBound
namespace CountingMatroid.Analysis.ConditionalDefectCoefficientBounds
end CountingMatroid.Analysis.ConditionalDefectCoefficientBounds
namespace CountingMatroid.Analysis.ObservableEnergyDual
end CountingMatroid.Analysis.ObservableEnergyDual
namespace CountingMatroid.Analysis.StationaryCovarianceSum
end CountingMatroid.Analysis.StationaryCovarianceSum
namespace CountingMatroid.Analysis.FinitePhaseEstimationBound
end CountingMatroid.Analysis.FinitePhaseEstimationBound
namespace CountingMatroid.Analysis.ObservationRoundDrawSites
end CountingMatroid.Analysis.ObservationRoundDrawSites
namespace CountingMatroid.Analysis.ClassifiedStateSelection
end CountingMatroid.Analysis.ClassifiedStateSelection
namespace CountingMatroid.Analysis.BoundedUniformSubkernel
end CountingMatroid.Analysis.BoundedUniformSubkernel
namespace CountingMatroid.Analysis.BoundedUniformSuccessWords
end CountingMatroid.Analysis.BoundedUniformSuccessWords
namespace CountingMatroid.Analysis.RestartPhaseTransversal
end CountingMatroid.Analysis.RestartPhaseTransversal
namespace CountingMatroid.Analysis.RestartPhaseIntervalReplay
end CountingMatroid.Analysis.RestartPhaseIntervalReplay
namespace CountingMatroid.Analysis.TraceReturnIntervalReplay
end CountingMatroid.Analysis.TraceReturnIntervalReplay
namespace CountingMatroid.Analysis.FiniteStoppedKernelBind
end CountingMatroid.Analysis.FiniteStoppedKernelBind
section


set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

/-! Compose covered operational positive-time returns while retaining their
shared attempt counter and the actual cursor between returns. -/
namespace CountingMatroid.Analysis.CappedTraceIterationSubkernel
open CountingMatroid.Model CountingMatroid.Program
open CountingMatroid.Analysis.FiniteStoppedFiberMass
open CountingMatroid.Analysis.PositiveTimeTraceKernel



/-- INTERNAL: Aborted trace folds remain aborted. -/
theorem trace_fold_none {n : ℕ} (r : ℕ) (o₁ o₂ : IndependenceOracle n)
    (tape : ℕ → Bool) (s : AnnealingSchedule) (q : ℚ) (w : Multipliers n)
    (xs : List ℕ) : traceFold r o₁ o₂ tape s q w xs none = none := by
  induction xs with
  | nil => rfl
  | cons a xs ih =>
    simpa only [traceFold, Arlib.Computation.Charged.val_foldl_cons,
      Arlib.Computation.Charged.val_pure] using ih

/-- INTERNAL: Split off one actual positive-time return, preserving its cursor. -/
theorem trace_fold_cons {n : ℕ} (r : ℕ) (o₁ o₂ : IndependenceOracle n)
    (tape : ℕ → Bool) (s : AnnealingSchedule) (q : ℚ) (w : Multipliers n)
    (a : ℕ) (xs : List ℕ) (current : RestartCursor n) :
    traceFold r o₁ o₂ tape s q w (a::xs) (some current) =
      ((traceReturn r o₁ o₂ tape s q w current).val).bind
        (fun next => traceFold r o₁ o₂ tape s q w xs (some next)) := by
  unfold traceFold
  rw [Arlib.Computation.Charged.val_foldl_cons]
  cases h : (traceReturn r o₁ o₂ tape s q w current).val with
  | none => exact trace_fold_none r o₁ o₂ tape s q w xs
  | some next => rfl





end CountingMatroid.Analysis.CappedTraceIterationSubkernel

/-! ### Run record
Newest first. History, not instruction — what this file claims is above.

* 2026-10-09 · proved · absorbing-option return folds replay consumed intervals and are dominated by ideal return iteration while preserving shared attempts and abort mass.
-/

end

section


set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

/-!
The number of `chainStep` attempts made by one actual positive-time return,
as a value recursion. The instrumented return adds exactly this number to its
retained counter, including the attempt that ends in a draw abort. On a fresh
finite suffix whose every attempted step stays inside the block, the chance of
making more than m attempts is at most the ideal positive-time survival tail.
-/
namespace CountingMatroid.Analysis.ReturnAttemptTail

open CountingMatroid.Model CountingMatroid.Program
open CountingMatroid.Analysis.FiniteStoppedFiberMass
open CountingMatroid.Analysis.PositiveTimeTraceKernel
open CountingMatroid.Analysis.RestartAttemptAccounting
open Arlib.Probability Arlib.MarkovChains











/-- INTERNAL: Tail weights are nonnegative. -/
theorem tailWeight_nonneg {Ω : Type} [Fintype Ω] [DecidableEq Ω]
    (P : FinChain Ω) (A : Finset Ω) (m : ℕ) (x : Ω) : 0 ≤ tailWeight P A m x := by
  cases m with
  | zero => simp [tailWeight]
  | succ m =>
      exact Finset.sum_nonneg fun z _ => mul_nonneg (P.coe_nonneg x z) (survive_nonneg P A m z)









end CountingMatroid.Analysis.ReturnAttemptTail

/-! ### Run record
Newest first. History, not instruction — what this file claims is above.

* 2026-10-09 · created · per-return attempt recursion, exact retained-count identity for the instrumented return, occupation budget as tail sums, and the covered attempt-tail bound.
-/

end

section


set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

/-!
Warm starts for every positive-time return of the restart that follows a
reached history with good stored multipliers. The cursor before return k of
stage i is the actual stopped restart cursor; its covered finite-suffix
state sublaw is at most four times the target-conditioned stationary law of
that stage's chain. The first stage starts from the fresh uniform transversal,
later stages from the scheduled factor-two mixing bound, and parameter drift
costs a further factor of two. Within a stage, capped returns are
sub-stationary. Aborted cursors carry no mass and are not renormalised.
-/
namespace CountingMatroid.Analysis.RestartStageWarmStart

open CountingMatroid.Model CountingMatroid.Program
open CountingMatroid.Analysis.FiniteStoppedFiberMass
open CountingMatroid.Analysis.PositiveTimeTraceKernel
open CountingMatroid.Analysis.CappedTraceIterationSubkernel
open CountingMatroid.Analysis.CappedRestartFinalTraceDomination
open CountingMatroid.Analysis.RestartAttemptAccounting



/-- INTERNAL: A stage's cursors continue the earlier stopped restart. -/
theorem stage_cursor_bind {n : ℕ} (r : ℕ) (o₁ o₂ : IndependenceOracle n)
    (tape : ℕ → Bool) (s : AnnealingSchedule) (tables : LearnedWeights n)
    (cursor i k : ℕ) :
    stageCursor r o₁ o₂ tape s tables cursor i k =
      (restart_phase_cursor r o₁ o₂ tape s tables i cursor).bind (fun c =>
        traceFold r o₁ o₂ tape s (s.ρ ^ (i + 1)) (tables (i + 1)) (List.range k) (some c)) := by
  unfold stageCursor
  cases restart_phase_cursor r o₁ o₂ tape s tables i cursor with
  | none => exact trace_fold_none r o₁ o₂ tape s _ _ _
  | some c => rfl





/-- INTERNAL: Trace folds keep their cursors transversal. -/
theorem trace_fold_transversal {n : ℕ} (r : ℕ) (o₁ o₂ : IndependenceOracle n)
    (tape : ℕ → Bool) (s : AnnealingSchedule) (q : ℚ) (w : Multipliers n)
    (xs : List ℕ) (c out : RestartCursor n)
    (hc : (classifyState c.state).val = .transversal)
    (h : traceFold r o₁ o₂ tape s q w xs (some c) = some out) :
    (classifyState out.state).val = .transversal := by
  induction xs generalizing c with
  | nil => cases Option.some.inj h; exact hc
  | cons a xs ih =>
      rw [trace_fold_cons] at h
      obtain ⟨middle, hm, ht⟩ := Option.bind_eq_some_iff.mp h
      exact ih middle (RestartPhaseTransversal.traceReturn_transversal r o₁ o₂ tape s q w
        c middle hm) ht

/-- INTERNAL: Every stage cursor is a transversal.
TEXLINE: main.tex:1163-1176 -/
theorem stage_cursor_transversal {n : ℕ} (r : ℕ) (o₁ o₂ : IndependenceOracle n)
    (tape : ℕ → Bool) (s : AnnealingSchedule) (tables : LearnedWeights n)
    (cursor i k : ℕ) (c : RestartCursor n)
    (h : stageCursor r o₁ o₂ tape s tables cursor i k = some c) :
    (classifyState c.state).val = .transversal := by
  rw [stage_cursor_bind] at h
  obtain ⟨start, hs, ht⟩ := Option.bind_eq_some_iff.mp h
  apply trace_fold_transversal r o₁ o₂ tape s _ _ _ start c _ ht
  have hp := restart_phase_cursor_projection r o₁ o₂ tape s tables i cursor
  rw [hs] at hp
  exact RestartPhaseTransversal.restartPhase_transversal r o₁ o₂ tape s tables i cursor
    (start.state, start.bitCursor) hp



/-- INTERNAL: A permitted attempt keeps the budget. -/
theorem budget_step {n : ℕ} (s : AnnealingSchedule) (base C : ℕ) (c : RestartCursor n)
    (y : PairedSet n) (stop : ℕ) (hc : Budget s base C c)
    (ha : c.attempts < s.restartCap) (hstop : stop ≤ c.bitCursor + C) :
    Budget s base C ⟨y, stop, c.attempts + 1⟩ := by
  obtain ⟨_, hb⟩ := hc
  refine ⟨by dsimp only; omega, ?_⟩
  dsimp only
  rw [Nat.add_mul, Nat.one_mul]
  omega







/-- INTERNAL: One covered operational chain step is dominated by the ideal
Metropolis kernel at the same level.
TEXLINE: main.tex:746-757,1392-1421 -/
theorem covered_step_bound {n : ℕ} (r : ℕ) (o₁ o₂ : IndependenceOracle n)
    (trials : ℕ) (q : ℚ) (w : Multipliers n) (hn : 0 < n) (hq : 0 < q)
    (hw : ∀ a, 0 < w a) (head : List Bool) (u : ℕ) (x y : PairedSet n)
    (hv : (classifyState x).val ≠ .invalid) :
    fairMass head u (fun tape => ∃ stop, stop ≤ head.length + u ∧
      (chainStep r o₁ o₂ tape trials q w x head.length).val = some (y, stop)) ≤
      IdealExchangeChain.idealChain r o₁ o₂ q w hn hq hw x y := by
  have hb := CoveredChainStepSubkernel.covered_chain_step_subkernel r o₁ o₂ trials q
    w hn hq hw head u x y (RecordedTraceContinuationBound.classified_card x hv) hv
  convert hb using 1
  unfold FiniteStoppedFiberMass.fairMass CoveredChainStepSubkernel.coveredChainStepMass
  apply Finset.sum_congr rfl
  intro suffix _
  unfold FiniteStoppedFiberMass.finiteTape
  split_ifs <;> rfl































end CountingMatroid.Analysis.RestartStageWarmStart

/-! ### Run record
Newest first. History, not instruction — what this file claims is above.

* 2026-10-09 · created · stage cursors with shared-cap budget and transversality, covered stage sublaws, composition through capped ideal returns, fresh-start and scheduled-mixing start bounds with parameter drift, and the factor-four warm start for every return.
-/

end
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

/-!
One stored stage of the restart after a reached history. The instrumented
stage adds to its retained counter exactly the attempts of its τ returns,
each made from the actual stopped cursor, including an attempt ending in a
draw abort. On the fresh finite suffix, the mean of that increment is at
most τ times the warm occupation budget 4/π(A) · occupation(π) of the stage's
chain: each return starts from a sublaw at most 4/π(A) times the restricted
stationary law, and makes more than m attempts with at most the ideal
positive-time survival tail.
-/
namespace CountingMatroid.Analysis.RestartStageAttemptMean
end CountingMatroid.Analysis.RestartStageAttemptMean
open CountingMatroid CountingMatroid.Analysis CountingMatroid.Analysis.RestartStageAttemptMean

open CountingMatroid.Model CountingMatroid.Program
open CountingMatroid.Analysis.FiniteStoppedFiberMass
open CountingMatroid.Analysis.PositiveTimeTraceKernel
open CountingMatroid.Analysis.CappedTraceIterationSubkernel
open CountingMatroid.Analysis.RestartAttemptAccounting
open CountingMatroid.Analysis.RestartStageWarmStart
open CountingMatroid.Analysis.ReturnAttemptTail

/-- INTERNAL: One stored stage's finite-suffix mean is at most τ warm
occupation budgets of its own chain.
TEXLINE: main.tex:1072-1087,1219-1234,1392-1421 -/
theorem solution (n r : ℕ)
    (M₁ M₂ : Matroid (Fin n)) (o₁ o₂ : IndependenceOracle n)
    (p : InputParams) (hn : 0 < n) (hfull : FullGround M₁ M₂)
    (hr : CommonRank r M₁ M₂) (h₁ : ExactOracle M₁ o₁)
    (h₂ : ExactOracle M₂ o₂) (j : ℕ)
    (hj : j < (CountingMatroid.Interface.Pseudocode.setup n p).L)
    (pref : List Bool) (history : RestartPrefixWitness n r o₁ o₂ p j pref)
    (i : ℕ) (hi : i < j)
    (hq : 0 < (CountingMatroid.Interface.Pseudocode.setup n p).ρ ^ (i + 1))
    (hw : ∀ a, 0 < history.current.tables (i + 1) a) :
    let s := CountingMatroid.Interface.Pseudocode.setup n p
    let t := CountingMatroid.Model.Run.blockLength n r p - pref.length
    let π := IdealExchangeChain.operationalLaw r o₁ o₂ (s.ρ ^ (i + 1))
      (history.current.tables (i + 1)) hq hw
    let P := IdealExchangeChain.idealChain r o₁ o₂ (s.ρ ^ (i + 1))
      (history.current.tables (i + 1)) hn hq hw
    let A := Finset.univ.filter (fun z : PairedSet n => (classifyState z).val = .transversal)
    (∑ bits : List.Vector Bool t,
      (stageAttempts r o₁ o₂ (finiteTape (pref ++ bits.val)) s history.current.tables
        history.current.bitCursor i : ℝ)) / (2 : ℝ) ^ t ≤
      (s.τ : ℝ) * (4 / (∑ z ∈ A, π z) *
        StationaryReturnOccupation.returnOccupation P A π s.restartCap) := by
  classical
  intro s t π P A
  let tables := history.current.tables
  let b0 := history.current.bitCursor
  let q := s.ρ ^ (i + 1)
  let w := tables (i + 1)
  let m := CountingMatroid.Model.Run.blockLength n r p
  obtain ⟨C, hlen, _, htotal, hCm, hCstep⟩ :=
    history_prefix_facts n r o₁ o₂ p hn j hj pref history
  change pref.length = b0 at hlen
  change pref.length + t = m at htotal
  change b0 + n + s.restartCap * C ≤ m at hCm
  have hj' : j < s.L := hj
  have hlevel : i + 1 ≤ s.L := by omega
  have hbudget (tape : ℕ → Bool) (k : ℕ) (c : RestartCursor n)
      (h : stageCursor r o₁ o₂ tape s tables b0 i k = some c) :
      Budget s (b0 + n) C c :=
    stage_cursor_budget r o₁ o₂ tape s tables b0 C i
      (fun a ha state start out hs => hCstep a (by omega) tape state start out hs) k c h
  have hinv : ∀ (tape : ℕ → Bool) (current : RestartCursor n) (y : PairedSet n) (stop : ℕ),
      Budget s (b0 + n) C current → current.attempts < s.restartCap →
      (chainStep r o₁ o₂ tape s.drawTrials q w current.state current.bitCursor).val =
        some (y, stop) →
      stop ≤ m ∧ Budget s (b0 + n) C ⟨y, stop, current.attempts + 1⟩ := by
    intro tape current y stop hc ha hs
    have hstop := hCstep (i + 1) hlevel tape current.state current.bitCursor (y, stop) hs
    have hb := budget_step s (b0 + n) C current y stop hc ha hstop
    refine ⟨?_, hb⟩
    obtain ⟨hatt, hcur⟩ := hc
    have hmul : (current.attempts + 1) * C ≤ s.restartCap * C :=
      Nat.mul_le_mul_right C (by omega)
    change stop ≤ current.bitCursor + C at hstop
    rw [Nat.add_mul, Nat.one_mul] at hmul
    omega
  have hcover (tape : ℕ → Bool) (k : ℕ) (c : RestartCursor n)
      (h : stageCursor r o₁ o₂ tape s tables b0 i k = some c) :
      c.bitCursor ≤ pref.length + t := by
    obtain ⟨hatt, hcur⟩ := hbudget tape k c h
    have hmul : c.attempts * C ≤ s.restartCap * C := Nat.mul_le_mul_right C hatt
    rw [htotal]
    omega
  -- The mean of one return's attempts is bounded by tail weights of its start law.
  have hreturn (k : ℕ) :
      (∑ bits : List.Vector Bool t, (1 / (2 : ℝ) ^ t) *
        ((((stageCursor r o₁ o₂ (finiteTape (pref ++ bits.val)) s tables b0 i k).map
          (attemptScan r o₁ o₂ (finiteTape (pref ++ bits.val)) s q w s.restartCap)).getD 0 : ℕ)
            : ℝ)) ≤
      ∑ mm ∈ Finset.range (s.restartCap + 1), ∑ x,
        (4 / ∑ z ∈ A, π z) * (if x ∈ A then π x else 0) *
          tailWeight P A mm x := by
    rw [layer_mass pref t (s.restartCap + 1)
      (fun tape => stageCursor r o₁ o₂ tape s tables b0 i k)
      (fun tape c => attemptScan r o₁ o₂ tape s q w s.restartCap c)
      (fun tape c => (attempt_scan_le r o₁ o₂ tape s q w s.restartCap c).trans
        (Nat.le_succ _))]
    apply Finset.sum_le_sum
    intro mm _
    have hf : ChainStepIntervalReplay.SuccessReplay
        (fun tape => stageCursor r o₁ o₂ tape s tables b0 i k)
        RestartCursor.bitCursor pref.length := by
      rw [hlen]
      exact stage_cursor_success_interval r o₁ o₂ s tables b0 i k
    have hbind := FiniteStoppedKernelBind.stopped_kernel_bind_covered_bound pref t
      (fun tape => stageCursor r o₁ o₂ tape s tables b0 i k)
      RestartCursor.bitCursor RestartCursor.state hf
      (fun tape c => mm + 1 ≤ attemptScan r o₁ o₂ tape s q w s.restartCap c)
      (fun x => tailWeight P A mm x) (fun x => tailWeight_nonneg P A mm x)
      (fun bits c hc _ => hcover _ k c hc)
      (by
        intro c hlo hhi head hc
        have hhead : (pref ++ head.val).length = c.bitCursor := by
          simp only [List.length_append, head.2]
          omega
        have hv : (classifyState c.state).val ≠ .invalid := by
          rw [stage_cursor_transversal r o₁ o₂ _ s tables b0 i k c hc]
          intro h
          cases h
        exact attempt_scan_tail r o₁ o₂ s q w P
          (fun head' u x y hx => covered_step_bound r o₁ o₂ s.drawTrials q w hn hq hw
            head' u x y hx)
          (Budget s (b0 + n) C) m hinv s.restartCap mm (pref ++ head.val)
          (t - (c.bitCursor - pref.length)) c hhead.symm
          (by rw [hhead]; omega) hv (hbudget _ k c hc))
    apply hbind.trans
    apply Finset.sum_le_sum
    intro x _
    apply mul_le_mul_of_nonneg_right _ (tailWeight_nonneg P A mm x)
    exact stage_warm_start n r M₁ M₂ o₁ o₂ p hn hfull hr h₁ h₂ j hj pref history i hi k
      hq hw x
  have hmean : (∑ bits : List.Vector Bool t,
      (stageAttempts r o₁ o₂ (finiteTape (pref ++ bits.val)) s tables b0 i : ℝ)) /
        (2 : ℝ) ^ t =
      ∑ k ∈ Finset.range s.τ, ∑ bits : List.Vector Bool t, (1 / (2 : ℝ) ^ t) *
        ((((stageCursor r o₁ o₂ (finiteTape (pref ++ bits.val)) s tables b0 i k).map
          (attemptScan r o₁ o₂ (finiteTape (pref ++ bits.val)) s q w s.restartCap)).getD 0 : ℕ)
            : ℝ) := by
    rw [Finset.sum_div, Finset.sum_comm]
    apply Finset.sum_congr rfl
    intro bits _
    unfold stageAttempts
    push_cast
    rw [Finset.sum_div]
    apply Finset.sum_congr rfl
    intro k _
    ring
  change (∑ bits : List.Vector Bool t,
      (stageAttempts r o₁ o₂ (finiteTape (pref ++ bits.val)) s tables b0 i : ℝ)) /
        (2 : ℝ) ^ t ≤ _
  rw [hmean]
  calc
    _ ≤ ∑ _k ∈ Finset.range s.τ, ∑ mm ∈ Finset.range (s.restartCap + 1), ∑ x,
          (4 / ∑ z ∈ A, π z) * (if x ∈ A then π x else 0) * tailWeight P A mm x :=
      Finset.sum_le_sum fun k _ => hreturn k
    _ = (s.τ : ℝ) * (4 / (∑ z ∈ A, π z) *
          StationaryReturnOccupation.returnOccupation P A π s.restartCap) := by
      rw [Finset.sum_const, Finset.card_range, nsmul_eq_mul,
        return_occupation_eq_tail_sum P A π s.restartCap]
      congr 1
      rw [Finset.sum_comm, Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro x _
      rw [Finset.mul_sum, Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro mm _
      ring
