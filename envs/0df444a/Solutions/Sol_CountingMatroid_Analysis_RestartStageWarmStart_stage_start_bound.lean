-- Prove2me | solution 1 for CountingMatroid.Analysis.RestartStageWarmStart.stage_start_bound
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-10-24T16:41:00.421998+00:00
-- url     : https://prove2.me/submissions/78fc119b-de8b-4887-b04b-5c7997f5175c

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
import Theorems.Thm_CountingMatroid_Analysis_AnnealingPartitionDrift_partition_step_bounds
import Theorems.Thm_CountingMatroid_Analysis_CappedRestartFinalTraceDomination_restart_phase_cursor_projection
import Theorems.Thm_CountingMatroid_Analysis_DefectPartitionPositive_defect_partition_pos
import Theorems.Thm_CountingMatroid_Analysis_PositiveTimeTraceKernel_endpoint_mass_le_of_capped_trace
import Theorems.Thm_CountingMatroid_Analysis_RestartPhaseTransversal_restartPhase_transversal
import Theorems.Thm_CountingMatroid_Analysis_RestartPhaseTransversal_traceReturn_transversal
import Theorems.Thm_CountingMatroid_Analysis_RestartStageWarmStart_fresh_stage_mass_le
import Theorems.Thm_CountingMatroid_Analysis_RestartStageWarmStart_history_prefix_facts
import Theorems.Thm_CountingMatroid_Analysis_RestartStageWarmStart_option_state_sum_le
import Theorems.Thm_CountingMatroid_Analysis_RestartStageWarmStart_stage_mass_fold
import Theorems.Thm_CountingMatroid_Analysis_ScheduledTransversalTraceMixing_scheduled_transversal_trace_mixing

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

/-! Finite uniform tape disintegration at a successful fixed endpoint cursor. -/
namespace CountingMatroid.Analysis.FiniteStoppedFiberMass













/-- INTERNAL: Event mass is nonnegative. -/
theorem fairMass_nonneg (head : List Bool) (t : ℕ) (E : (ℕ → Bool) → Prop) :
    0 ≤ fairMass head t E := by
  classical
  exact Finset.sum_nonneg (fun _ _ => by split_ifs <;> positivity)







end CountingMatroid.Analysis.FiniteStoppedFiberMass

end

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
The last-stage finite-suffix comparison for a successful phase prefix. Its
reference starts with the actual preceding-stage sublaw and grants each final
trace return the full cap, which can only add mass relative to the shared
operational attempt cap. Stopped-prefix disintegration, positive-time return
composition, and deterministic finite-block coverage prove the comparison.
-/
namespace CountingMatroid.Analysis.CappedRestartFinalTraceDomination

open CountingMatroid.Model CountingMatroid.Program
open CountingMatroid.Analysis.PhaseObservationExperiment





/-- INTERNAL: A charged list fold splits without discarding the prefix value. -/
private theorem cursor_fold_append {α β : Type}
    (f : β → α → Arlib.Computation.Charged Model.Operations.Op Model.Operations.Cell β)
    (xs ys : List α) (b : β) :
    (Arlib.Computation.Charged.foldl f (xs ++ ys) b).val =
      (Arlib.Computation.Charged.foldl f ys
        (Arlib.Computation.Charged.foldl f xs b).val).val := by
  induction xs generalizing b with
  | nil => rfl
  | cons x xs ih =>
      simpa only [List.cons_append, Arlib.Computation.Charged.val_foldl_cons]
        using ih (f b x).val



/-- INTERNAL: Split off the final stage without resetting the shared attempts
counter, drawing a second initial transversal, or forgetting the stopping cursor.
TEXLINE: main.tex:1163-1176 -/
theorem restart_phase_cursor_succ {n : ℕ} (r : ℕ)
    (o₁ o₂ : IndependenceOracle n) (tape : ℕ → Bool)
    (s : AnnealingSchedule) (tables : LearnedWeights n) (j cursor : ℕ) :
    restart_phase_cursor r o₁ o₂ tape s tables (j + 1) cursor =
      (restart_stage r o₁ o₂ tape s tables j
        (restart_phase_cursor r o₁ o₂ tape s tables j cursor)).val := by
  unfold restart_phase_cursor
  simp only [Arlib.Computation.Charged.repeatFor]
  rw [List.range_succ, cursor_fold_append]
  rfl





/-- INTERNAL: Expose a stage as the fold to which the covered trace-return
composition theorem applies. No attempt counter is reset.
TEXLINE: main.tex:1163-1176 -/
theorem restart_stage_eq_trace_fold {n : ℕ} (r : ℕ)
    (o₁ o₂ : IndependenceOracle n) (tape : ℕ → Bool)
    (s : AnnealingSchedule) (tables : LearnedWeights n) (index : ℕ)
    (current : RestartCursor n) :
    (restart_stage r o₁ o₂ tape s tables index (some current)).val =
      CappedTraceIterationSubkernel.traceFold r o₁ o₂ tape s (s.ρ ^ (index+1))
        (tables (index+1)) (List.range s.τ) (some current) := by
  unfold restart_stage CappedTraceIterationSubkernel.traceFold
  simp only [Arlib.Computation.Charged.val_bind, Model.Operations.successor,
    Arlib.Computation.Charged.val_op, CountingMatroid.Analysis.BoundedRunResourceEnvelope.ratPower_value_import_support,
    Model.Operations.learnedWeightRead, Arlib.Computation.Charged.val_opMany,
    Arlib.Computation.Charged.repeatFor]
  rfl













end CountingMatroid.Analysis.CappedRestartFinalTraceDomination

/-! ### Run record
Newest first. History, not instruction — what this file claims is above.

* 2026-10-09 · dependency-blocked · final recheck cannot load CountingMatroid.Analysis.CoveredChainStepSubkernel because its object is unavailable after the concurrent dependency build failed; the target and every new helper had already passed standalone elaboration. No local proof obligation remains open, and the active dependency source was not edited.

* 2026-10-09 · verified · standalone elaboration closes the target with no local proof gaps; all four support modules built. Parent publication encountered concurrent CoveredChainStepSubkernel compiler errors at lines 142–147, so no edits were made to that dependency.

* 2026-10-09 · proved · closed capped_restart_final_trace_domination through proved stopped-result disintegration, globally capped return-scan recursion, covered trace iteration, and restart-only block coverage; preserved the statement, old imports, and preceding proof progress.

* 2026-10-09 · exposed · last-stage finite-suffix domination uses the concrete positive-time return kernel; direct one-step application has the wrong event and cursor index. The independent stopping-prefix composition is ready for the live OPEN handoff.
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

/-- INTERNAL: The next stage starts where all τ returns of a stage end.
TEXLINE: main.tex:1163-1176 -/
theorem stage_cursor_next {n : ℕ} (r : ℕ) (o₁ o₂ : IndependenceOracle n)
    (tape : ℕ → Bool) (s : AnnealingSchedule) (tables : LearnedWeights n)
    (cursor i : ℕ) :
    stageCursor r o₁ o₂ tape s tables cursor (i + 1) 0 =
      stageCursor r o₁ o₂ tape s tables cursor i s.τ := by
  change restart_phase_cursor r o₁ o₂ tape s tables (i + 1) cursor = _
  rw [restart_phase_cursor_succ, stage_cursor_bind]
  cases restart_phase_cursor r o₁ o₂ tape s tables i cursor with
  | none =>
      simp only [restart_stage, Arlib.Computation.Charged.val_pure, Option.bind_none]
  | some c =>
      rw [restart_stage_eq_trace_fold]
      rfl



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















/-- INTERNAL: Stage masses are nonnegative. -/
theorem stage_mass_nonneg {n : ℕ} (r : ℕ) (o₁ o₂ : IndependenceOracle n)
    (s : AnnealingSchedule) (tables : LearnedWeights n) (cursor : ℕ)
    (pref : List Bool) (t i k : ℕ) (x : PairedSet n) :
    0 ≤ stageMass r o₁ o₂ s tables cursor pref t i k x :=
  fairMass_nonneg _ _ _

/-- INTERNAL: Stage masses vanish off the transversals. -/
theorem stage_mass_off {n : ℕ} (r : ℕ) (o₁ o₂ : IndependenceOracle n)
    (s : AnnealingSchedule) (tables : LearnedWeights n) (cursor : ℕ)
    (pref : List Bool) (t i k : ℕ) (x : PairedSet n)
    (hx : (classifyState x).val ≠ .transversal) :
    stageMass r o₁ o₂ s tables cursor pref t i k x = 0 := by
  classical
  unfold stageMass fairMass
  apply Finset.sum_eq_zero
  intro bits _
  apply if_neg
  rintro ⟨c, hc, _, hs⟩
  exact hx (hs ▸ stage_cursor_transversal r o₁ o₂ _ s tables cursor i k c hc)



/-- INTERNAL: A stage sublaw has total mass at most one. -/
theorem stage_mass_sum_le_one {n : ℕ} (r : ℕ) (o₁ o₂ : IndependenceOracle n)
    (s : AnnealingSchedule) (tables : LearnedWeights n) (cursor : ℕ)
    (pref : List Bool) (t i k : ℕ) :
    (∑ x, stageMass r o₁ o₂ s tables cursor pref t i k x) ≤ 1 := by
  classical
  unfold stageMass fairMass
  rw [Finset.sum_comm]
  calc
    _ ≤ ∑ _ : List.Vector Bool t, 1 / (2 : ℝ) ^ t := by
      apply Finset.sum_le_sum
      intro bits _
      exact @option_state_sum_le n _ _ (fun _ => Classical.propDecidable _) (1 / (2 : ℝ) ^ t) (by positivity)
    _ = 1 := by simp [card_vector]







/-- INTERNAL: At q = 1 every transversal has conditioned mass 2^-n.
TEXLINE: main.tex:1242-1244 -/
theorem transversal_law_one {n : ℕ} (r : ℕ) (o₁ o₂ : IndependenceOracle n)
    (x : PairedSet n) (hx : (classifyState x).val = .transversal) :
    transversalLaw r o₁ o₂ 1 x = 1 / (2 : ℝ) ^ n := by
  have hC : TransversalPartition.partitionSum r o₁ o₂ 1 = (2 : ℚ) ^ n := by
    simp [TransversalPartition.partitionSum]
  simp [transversalLaw, hx, hC]







/-- INTERNAL: Stored tables up to the current phase are positive.
TEXLINE: main.tex:1201-1205 -/
theorem history_table_pos (n r : ℕ) (o₁ o₂ : IndependenceOracle n)
    (p : InputParams) (hn : 0 < n) (j : ℕ) (pref : List Bool)
    (history : RestartPrefixWitness n r o₁ o₂ p j pref) (a : ℕ) (ha : a ≤ j)
    (index : DefectIndex n) : 0 < history.current.tables a index := by
  let s := CountingMatroid.Interface.Pseudocode.setup n p
  have hq : 0 < s.ρ ^ a := pow_pos (AnnealingPartitionDrift.schedule_power_lower n p hn).1 a
  have hC : 0 < TransversalPartition.partitionSum r o₁ o₂ (s.ρ ^ a) :=
    (AnnealingPartitionDrift.partition_step_bounds n r o₁ o₂ p hn a).1
  exact (div_pos (div_pos hC
    (DefectPartitionPositive.defect_partition_pos r o₁ o₂ (s.ρ ^ a) hq index))
    (by norm_num : (0 : ℚ) < 4)).trans_le (history.good.1 a ha index).1





end CountingMatroid.Analysis.RestartStageWarmStart

/-! ### Run record
Newest first. History, not instruction — what this file claims is above.

* 2026-10-09 · created · stage cursors with shared-cap budget and transversality, covered stage sublaws, composition through capped ideal returns, fresh-start and scheduled-mixing start bounds with parameter drift, and the factor-four warm start for every return.
-/

end
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
end CountingMatroid.Analysis.RestartStageWarmStart
open CountingMatroid CountingMatroid.Analysis CountingMatroid.Analysis.RestartStageWarmStart

open CountingMatroid.Model CountingMatroid.Program
open CountingMatroid.Analysis.FiniteStoppedFiberMass
open CountingMatroid.Analysis.PositiveTimeTraceKernel
open CountingMatroid.Analysis.CappedTraceIterationSubkernel
open CountingMatroid.Analysis.CappedRestartFinalTraceDomination
open CountingMatroid.Analysis.RestartAttemptAccounting

/-- INTERNAL: Before its first return, stage i has covered sublaw at most twice
the conditioned transversal law at level i: exactly the fresh law when i = 0,
and the scheduled mixing bound of the preceding stage otherwise.
TEXLINE: main.tex:1215-1225,1242-1244 -/
theorem solution (n r : ℕ)
    (M₁ M₂ : Matroid (Fin n)) (o₁ o₂ : IndependenceOracle n)
    (p : InputParams) (hn : 0 < n) (hfull : FullGround M₁ M₂)
    (hr : CommonRank r M₁ M₂) (h₁ : ExactOracle M₁ o₁)
    (h₂ : ExactOracle M₂ o₂) (j : ℕ)
    (hj : j < (CountingMatroid.Interface.Pseudocode.setup n p).L)
    (pref : List Bool) (history : RestartPrefixWitness n r o₁ o₂ p j pref)
    (i : ℕ) (hi : i < j) (x : PairedSet n) :
    let s := CountingMatroid.Interface.Pseudocode.setup n p
    let t := CountingMatroid.Model.Run.blockLength n r p - pref.length
    stageMass r o₁ o₂ s history.current.tables history.current.bitCursor pref t i 0 x ≤
      2 * transversalLaw r o₁ o₂ (s.ρ ^ i) x := by
  classical
  intro s t
  obtain ⟨C, hlen, hnt, _, _, _⟩ := history_prefix_facts n r o₁ o₂ p hn j hj pref history
  by_cases hx : (classifyState x).val = .transversal
  case neg =>
    rw [stage_mass_off r o₁ o₂ s _ _ pref t i 0 x hx]
    simp [transversalLaw, hx]
  cases i with
  | zero =>
      have hf := fresh_stage_mass_le r o₁ o₂ s history.current.tables
        history.current.bitCursor pref t hlen hnt x
      rw [pow_zero, transversal_law_one r o₁ o₂ x hx]
      have hpos : (0 : ℝ) ≤ 1 / (2 : ℝ) ^ n := by positivity
      linarith
  | succ i =>
      let tables := history.current.tables
      let q := s.ρ ^ (i + 1)
      have hq : 0 < q := pow_pos (AnnealingPartitionDrift.schedule_power_lower n p hn).1 _
      have hw : ∀ a, 0 < tables (i + 1) a :=
        history_table_pos n r o₁ o₂ p hn j pref history (i + 1) (by omega)
      let P := IdealExchangeChain.idealChain r o₁ o₂ q (tables (i + 1)) hn hq hw
      let A := Finset.univ.filter (fun z : PairedSet n => (classifyState z).val = .transversal)
      have hnext : stageMass r o₁ o₂ s tables history.current.bitCursor pref t (i + 1) 0 x =
          stageMass r o₁ o₂ s tables history.current.bitCursor pref t i s.τ x := by
        unfold stageMass
        simp only [stage_cursor_next]
      rw [hnext]
      have hfold := stage_mass_fold r o₁ o₂ s tables history.current.bitCursor pref t i s.τ
        hn hq hw hlen.le x
      have hxA : x ∈ TransversalTraceSpectralGap.transversalSet n := by
        simpa only [TransversalTraceSpectralGap.transversalSet, Finset.mem_filter,
          Finset.mem_univ, true_and] using hx
      apply PositiveTimeTraceKernel.endpoint_mass_le_of_capped_trace P A s.restartCap s.τ
        (fun y => stageMass r o₁ o₂ s tables history.current.bitCursor pref t i 0 y)
        (fun y => stage_mass_nonneg r o₁ o₂ s _ _ pref t i 0 y)
        (stage_mass_sum_le_one r o₁ o₂ s _ _ pref t i 0)
        (fun y hy => stage_mass_off r o₁ o₂ s _ _ pref t i 0 y (by
          simpa only [A, Finset.mem_filter, Finset.mem_univ, true_and] using hy))
        _ _ (by
          simp only [transversalLaw, hx, if_true]
          have hC : 0 < TransversalPartition.partitionSum r o₁ o₂ q :=
            (AnnealingPartitionDrift.partition_step_bounds n r o₁ o₂ p hn (i + 1)).1
          apply mul_nonneg (by norm_num)
          apply div_nonneg
          · exact_mod_cast pow_nonneg hq.le _
          · exact_mod_cast hC.le) x hfold
      intro y hy
      have hyA : y ∈ TransversalTraceSpectralGap.transversalSet n := by
        simpa only [TransversalTraceSpectralGap.transversalSet] using hy
      have hmix := ScheduledTransversalTraceMixing.scheduled_transversal_trace_mixing
        n r M₁ M₂ o₁ o₂ p (i + 1) (tables (i + 1)) hn hfull hr h₁ h₂ (by omega) hw
        (history.good.1 (i + 1) (by omega)) y x hyA hxA
      simpa only [P, A, q, TransversalTraceSpectralGap.transversalSet, transversalLaw, hx,
        if_true] using hmix
