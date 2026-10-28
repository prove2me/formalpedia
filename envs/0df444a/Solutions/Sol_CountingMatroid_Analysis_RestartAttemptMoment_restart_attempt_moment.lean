-- Prove2me | solution 1 for CountingMatroid.Analysis.RestartAttemptMoment.restart_attempt_moment
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-10-24T16:48:42.397514+00:00
-- url     : https://prove2.me/submissions/998b3646-5ded-4ffb-b751-fa1ce53137ba

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
import Definitions.Def_CountingMatroid_Analysis_RestartAttemptMoment
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
import Theorems.Thm_CountingMatroid_Analysis_DefectPartitionPositive_defect_partition_pos
import Theorems.Thm_CountingMatroid_Analysis_RestartStageAttemptMean_counted_transition_fold
import Theorems.Thm_CountingMatroid_Analysis_RestartStageAttemptMean_restart_stage_attempt_mean
import Theorems.Thm_CountingMatroid_Analysis_StationaryReturnOccupation_warm_return_occupation_le
import Theorems.Thm_CountingMatroid_Analysis_TypeMassLowerBounds_good_type_mass_bounds

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

namespace CountingMatroid.Analysis.IdealExchangeChain

open CountingMatroid.Model CountingMatroid.Program
open CountingMatroid.Analysis.StationaryMeanIdentities
open Arlib.Probability Arlib.MarkovChains























/-- INTERNAL: Identify the operational rational type mean with expectation
under the concrete ideal stationary law, for correlated-observation analysis.
TEXLINE: main.tex:1241-1247 -/
theorem operational_type_mean {n : ℕ} (r : ℕ) (o₁ o₂ : IndependenceOracle n)
    (q : ℚ) (w : Multipliers n) (hq : 0 < q) (hw : ∀ index, 0 < w index)
    (kind : StateKind n) :
    Ex (operationalLaw r o₁ o₂ q w hq hw) (typeIndicator kind) =
      (typeMean r o₁ o₂ q w kind : ℝ) := by
  classical
  unfold Ex typeMean
  push_cast
  rw [Finset.sum_div]
  apply Finset.sum_congr rfl
  intro state _
  by_cases hk : (classifyState state).val = kind
  · simp [operationalLaw, typeIndicator, hk]
  · simp [operationalLaw, typeIndicator, hk]





end CountingMatroid.Analysis.IdealExchangeChain

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

















































end CountingMatroid.Analysis.RestartStageWarmStart

/-! ### Run record
Newest first. History, not instruction — what this file claims is above.

* 2026-10-09 · created · stage cursors with shared-cap budget and transversality, covered stage sublaws, composition through capped ideal returns, fresh-start and scheduled-mixing start bounds with parameter drift, and the factor-four warm start for every return.
-/

end

section


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

open CountingMatroid.Model CountingMatroid.Program
open CountingMatroid.Analysis.FiniteStoppedFiberMass
open CountingMatroid.Analysis.PositiveTimeTraceKernel
open CountingMatroid.Analysis.CappedTraceIterationSubkernel
open CountingMatroid.Analysis.RestartAttemptAccounting
open CountingMatroid.Analysis.RestartStageWarmStart
open CountingMatroid.Analysis.ReturnAttemptTail









/-- INTERNAL: A stored stage's exact instrumented value.
TEXLINE: main.tex:1163-1176 -/
theorem counted_stage_value {n : ℕ} (r : ℕ) (o₁ o₂ : IndependenceOracle n)
    (tape : ℕ → Bool) (s : AnnealingSchedule) (tables : LearnedWeights n)
    (i : ℕ) (o : Option (RestartCursor n)) (count : ℕ) :
    (countedStage r o₁ o₂ tape s tables i (o, count)).val =
    (traceFold r o₁ o₂ tape s (s.ρ ^ (i + 1)) (tables (i + 1)) (List.range s.τ) o,
      count + ∑ k ∈ Finset.range s.τ,
        ((traceFold r o₁ o₂ tape s (s.ρ ^ (i + 1)) (tables (i + 1)) (List.range k) o).map
          (attemptScan r o₁ o₂ tape s (s.ρ ^ (i + 1)) (tables (i + 1)) s.restartCap)).getD 0) := by
  have h := counted_transition_fold r o₁ o₂ tape s (s.ρ ^ (i + 1)) (tables (i + 1)) s.τ o count
  simp only [countedStage, Arlib.Computation.Charged.val_bind, Model.Operations.successor,
    Arlib.Computation.Charged.val_op, CountingMatroid.Analysis.BoundedRunResourceEnvelope.ratPower_value_import_support,
    Model.Operations.learnedWeightRead, Arlib.Computation.Charged.val_opMany,
    Arlib.Computation.Charged.repeatFor]
  exact h







end CountingMatroid.Analysis.RestartStageAttemptMean

/-! ### Run record
Newest first. History, not instruction — what this file claims is above.

* 2026-10-09 · created · exact instrumented stage value, layer-cake identity for bounded stopped counts, and the stage mean bound from covered attempt tails and factor-four warm starts.
-/

end

section


set_option autoImplicit false

/-!
The stochastic half of the restart certificate: the finite-suffix mean of the
fixed, value-preserving stopped attempt counter is at most `20 n² L τ`.
The mean splits exactly into stage means (draw-abort attempts retained); each
stage's increment is identified with the attempt count of its τ actual returns,
whose mean `RestartStageAttemptMean.restart_stage_attempt_mean` bounds by τ warm
stationary occupation budgets, each at most `20 n²`. Constructing covered
integer-draw histories is a separate deterministic obligation.
-/
namespace CountingMatroid.Analysis.RestartAttemptMoment

open CountingMatroid.Model CountingMatroid.Program
open CountingMatroid.Analysis.RestartAttemptAccounting





/-- INTERNAL: Split the charged stage fold without dropping an abort count. -/
private theorem attempt_fold_append {α β : Type}
    (f : β → α → Arlib.Computation.Charged CountingMatroid.Model.Operations.Op
      CountingMatroid.Model.Operations.Cell β)
    (xs ys : List α) (b : β) :
    (Arlib.Computation.Charged.foldl f (xs ++ ys) b).val =
      (Arlib.Computation.Charged.foldl f ys
        (Arlib.Computation.Charged.foldl f xs b).val).val := by
  induction xs generalizing b with
  | nil => rfl
  | cons x xs ih =>
      simpa only [List.cons_append, Arlib.Computation.Charged.val_foldl_cons]
        using ih (f b x).val

/-- INTERNAL: Each stage increment is evaluated from the actual earlier
stopped accumulator, rather than from a separately chosen starting law.
TEXLINE: main.tex:1226-1234 -/
theorem restart_stage_state_succ {n r : ℕ} {o₁ o₂ : IndependenceOracle n}
    {p : InputParams} {j : ℕ} {pref : List Bool}
    (history : RestartPrefixWitness n r o₁ o₂ p j pref) (suffix : List Bool)
    (k : ℕ) :
    prefixRestartState history suffix (k + 1) =
      (countedStage r o₁ o₂ (fun i => ((pref ++ suffix)[i]?).getD false)
        (CountingMatroid.Interface.Pseudocode.setup n p) history.current.tables k
        (prefixRestartState history suffix k)).val := by
  unfold prefixRestartState Arlib.Computation.Charged.repeatFor
  rw [List.range_succ, attempt_fold_append]
  rfl











/-- INTERNAL: Stage increments telescope to the original stopped attempt
counter on every suffix, including executions ending in a draw abort.
TEXLINE: main.tex:1230-1234 -/
theorem prefix_stage_attempts_sum {n r : ℕ} {o₁ o₂ : IndependenceOracle n}
    {p : InputParams} {j : ℕ} {pref : List Bool}
    (history : RestartPrefixWitness n r o₁ o₂ p j pref) (suffix : List Bool) :
    (∑ i : Fin j, prefixStageAttempts history suffix i.val) =
      (prefixAttemptCost history suffix : ℝ) := by
  rw [Fin.sum_univ_eq_sum_range]
  unfold prefixStageAttempts
  rw [Finset.sum_range_sub (fun k => ((prefixRestartState history suffix k).2 : ℝ))]
  have hz : (prefixRestartState history suffix 0).2 = 0 := rfl
  rw [hz, Nat.cast_zero, sub_zero]
  rfl

/-- INTERNAL: The finite-suffix mean is exactly the sum of stage means;
no conditioning on completion removes the last attempt of an abort.
TEXLINE: main.tex:1230-1234,1392-1421 -/
theorem prefix_stage_attempt_mean_sum {n r : ℕ} {o₁ o₂ : IndependenceOracle n}
    {p : InputParams} {j : ℕ} {pref : List Bool}
    (history : RestartPrefixWitness n r o₁ o₂ p j pref) (t : ℕ) :
    (∑ bits : List.Vector Bool t, (prefixAttemptCost history bits.val : ℝ)) /
      (2 : ℝ) ^ t =
    ∑ i : Fin j, (∑ bits : List.Vector Bool t,
      prefixStageAttempts history bits.val i.val) / (2 : ℝ) ^ t := by
  simp_rw [← prefix_stage_attempts_sum history]
  rw [Finset.sum_comm, Finset.sum_div]

/-- INTERNAL: The cursor of the stopped accumulator after k stages is the
actual restart cursor at the start of stage k.
TEXLINE: main.tex:1163-1176 -/
theorem prefix_state_cursor {n r : ℕ} {o₁ o₂ : IndependenceOracle n}
    {p : InputParams} {j : ℕ} {pref : List Bool}
    (history : RestartPrefixWitness n r o₁ o₂ p j pref) (suffix : List Bool)
    (k : ℕ) :
    (prefixRestartState history suffix k).1 =
      RestartStageWarmStart.stageCursor r o₁ o₂
        (FiniteStoppedFiberMass.finiteTape (pref ++ suffix))
        (CountingMatroid.Interface.Pseudocode.setup n p) history.current.tables
        history.current.bitCursor k 0 := by
  induction k with
  | zero => rfl
  | succ k ih =>
      rw [RestartStageWarmStart.stage_cursor_next, restart_stage_state_succ,
        ← Prod.mk.eta (p := prefixRestartState history suffix k),
        RestartStageAttemptMean.counted_stage_value, ih]
      rfl

/-- INTERNAL: A stage's real increment is the attempt count of its τ returns.
TEXLINE: main.tex:1163-1176,1230-1234 -/
theorem prefix_stage_attempts_eq {n r : ℕ} {o₁ o₂ : IndependenceOracle n}
    {p : InputParams} {j : ℕ} {pref : List Bool}
    (history : RestartPrefixWitness n r o₁ o₂ p j pref) (suffix : List Bool)
    (k : ℕ) :
    prefixStageAttempts history suffix k =
      (RestartStageAttemptMean.stageAttempts r o₁ o₂
        (FiniteStoppedFiberMass.finiteTape (pref ++ suffix))
        (CountingMatroid.Interface.Pseudocode.setup n p) history.current.tables
        history.current.bitCursor k : ℝ) := by
  unfold prefixStageAttempts
  rw [restart_stage_state_succ,
    ← Prod.mk.eta (p := prefixRestartState history suffix k),
    RestartStageAttemptMean.counted_stage_value, prefix_state_cursor]
  rw [Nat.cast_add, add_sub_cancel_left]
  rfl



end CountingMatroid.Analysis.RestartAttemptMoment

/-! ### Run record
Newest first. History, not instruction — what this file claims is above.

* 2026-10-09 · proved · closed the one-stage bound with the (previously unattached, fully proved) `RestartStageAttemptMean.restart_stage_attempt_mean`, bridged by `prefix_state_cursor` and `prefix_stage_attempts_eq`; no `sorry` remains.

* 2026-10-09 · recovered stage decomposition · proved actual stage recurrence, nonnegative retained increments, and exact mean telescoping; replaced the whole-restart occupation gap by the one-stage mean bound, retaining the original theorem and one open proof.

* 2026-10-09 · repaired decomposition · proved finite stationary return occupation telescoping and its warm budget, instantiated every actual stored stage, and isolated the stopped finite-tape occupation comparison; preserved the theorem statement and its single open proof.

* 2026-10-09 · reduced · fixed the quantity to the proved restart instrument, closed zero stages, and exposed the positive-stage stopped-counter sum. Remaining work is occupation/survival comparison and warm stage propagation, not selection of a cost witness or construction of draw histories.
-/

end
set_option autoImplicit false

/-!
The stochastic half of the restart certificate: the finite-suffix mean of the
fixed, value-preserving stopped attempt counter is at most `20 n² L τ`.
The mean splits exactly into stage means (draw-abort attempts retained); each
stage's increment is identified with the attempt count of its τ actual returns,
whose mean `RestartStageAttemptMean.restart_stage_attempt_mean` bounds by τ warm
stationary occupation budgets, each at most `20 n²`. Constructing covered
integer-draw histories is a separate deterministic obligation.
-/
namespace CountingMatroid.Analysis.RestartAttemptMoment
end CountingMatroid.Analysis.RestartAttemptMoment
open CountingMatroid CountingMatroid.Analysis CountingMatroid.Analysis.RestartAttemptMoment

open CountingMatroid.Model CountingMatroid.Program
open CountingMatroid.Analysis.RestartAttemptAccounting

/-- INTERNAL: Transfer the paper's uncapped restart mean to the fixed counted
restart on the actual suffix, retaining attempts made before a draw abort.
The reached-history witness fixes both tables and cursor, rather than letting
the expectation proof choose an unrelated cost function.
TEXLINE: main.tex:1072-1087,1207-1234,1392-1421 -/
theorem solution (n r : ℕ)
    (M₁ M₂ : Matroid (Fin n)) (o₁ o₂ : IndependenceOracle n)
    (p : InputParams) (hn : 0 < n) (hfull : FullGround M₁ M₂)
    (hr : CommonRank r M₁ M₂) (h₁ : ExactOracle M₁ o₁)
    (h₂ : ExactOracle M₂ o₂) (hpositive : 0 < commonBaseCount M₁ M₂)
    (j : ℕ) (hj : j < (CountingMatroid.Interface.Pseudocode.setup n p).L)
    (pref : List Bool) (history : RestartPrefixWitness n r o₁ o₂ p j pref) :
    let s := CountingMatroid.Interface.Pseudocode.setup n p
    let t := CountingMatroid.Model.Run.blockLength n r p - pref.length
    (∑ bits : List.Vector Bool t, (prefixAttemptCost history bits.val : ℚ)) /
      (2 : ℚ) ^ t ≤ 20 * (n : ℚ) ^ 2 * (s.L : ℚ) * (s.τ : ℚ) := by
  dsimp only
  cases j with
  | zero =>
      simp only [prefixAttemptCost, countedRestart,
        Arlib.Computation.Charged.val_bind, Arlib.Computation.Charged.val_pure,
        Arlib.Computation.Charged.repeatFor, List.range_zero,
        Arlib.Computation.Charged.val_foldl_nil, Nat.cast_zero,
        Finset.sum_const_zero, zero_div]
      positivity
  | succ a =>
      classical
      let s := CountingMatroid.Interface.Pseudocode.setup n p
      let t := CountingMatroid.Model.Run.blockLength n r p - pref.length
      let q (i : Fin (a + 1)) := s.ρ ^ (i.val + 1)
      let w (i : Fin (a + 1)) := history.current.tables (i.val + 1)
      have hq (i : Fin (a + 1)) : 0 < q i :=
        pow_pos (AnnealingPartitionDrift.schedule_power_lower n p hn).1 _
      have hgood (i : Fin (a + 1)) := history.good.1 (i.val + 1) (by omega)
      have hw (i : Fin (a + 1)) (index : DefectIndex n) : 0 < w i index := by
        have hC : 0 < TransversalPartition.partitionSum r o₁ o₂ (q i) := by
          apply Finset.sum_pos
          · intro A _
            exact pow_pos (hq i) _
          · exact Finset.univ_nonempty
        exact (div_pos (div_pos hC
          (DefectPartitionPositive.defect_partition_pos r o₁ o₂ (q i) (hq i) index))
          (by norm_num : (0 : ℚ) < 4)).trans_le (hgood i index).1
      let μ (i : Fin (a + 1)) :=
        IdealExchangeChain.operationalLaw r o₁ o₂ (q i) (w i) (hq i) (hw i)
      let P (i : Fin (a + 1)) :=
        IdealExchangeChain.idealChain r o₁ o₂ (q i) (w i) hn (hq i) (hw i)
      let A : Finset (PairedSet n) :=
        Finset.univ.filter (fun state => (classifyState state).val = .transversal)
      let mass (i : Fin (a + 1)) := ∑ x ∈ A, μ i x
      let budget (i : Fin (a + 1)) :=
        4 / mass i * StationaryReturnOccupation.returnOccupation (P i) A (μ i) s.restartCap
      have hbudget (i : Fin (a + 1)) : budget i ≤ 20 * (n : ℝ) ^ 2 := by
        have hmass_eq : mass i =
            (StationaryMeanIdentities.typeMean r o₁ o₂ (q i) (w i) .transversal : ℝ) := by
          rw [← IdealExchangeChain.operational_type_mean r o₁ o₂ (q i) (w i)
            (hq i) (hw i) .transversal]
          simp only [mass, A, μ, Arlib.Probability.FinDist.Ex,
            IdealExchangeChain.typeIndicator, mul_ite, mul_one, mul_zero]
          exact Finset.sum_filter _ _
        have hmass_lower : 1 / (5 * (n : ℝ) ^ 2) ≤ mass i := by
          rw [hmass_eq]
          have hb := (Rat.cast_le (K := ℝ)).mpr
            (TypeMassLowerBounds.good_type_mass_bounds r o₁ o₂
              (q i) (w i) hn (hq i) (hgood i)).2.1
          push_cast at hb
          exact hb
        have hnreal : (0 : ℝ) < n := by exact_mod_cast hn
        have hmass : 0 < mass i :=
          (by positivity : (0 : ℝ) < 1 / (5 * (n : ℝ) ^ 2)).trans_le hmass_lower
        have hB : 1 ≤ (5 * (n : ℝ) ^ 2) * mass i := by
          have hb := (div_le_iff₀ (by positivity : (0 : ℝ) < 5 * (n : ℝ) ^ 2)).mp hmass_lower
          simpa only [mul_comm] using hb
        have hb := StationaryReturnOccupation.warm_return_occupation_le
          (P i) A (μ i)
          (IdealExchangeChain.ideal_chain_stationary r o₁ o₂ (q i) (w i) hn (hq i) (hw i))
          s.restartCap 4 (5 * (n : ℝ) ^ 2) (by norm_num) hmass hB
        change budget i ≤ 4 * (5 * (n : ℝ) ^ 2) at hb
        nlinarith
      have hstage (i : Fin (a + 1)) :
          (∑ bits : List.Vector Bool t,
            prefixStageAttempts history bits.val i.val) / (2 : ℝ) ^ t ≤
              (s.τ : ℝ) * budget i := by
        have hm := RestartStageAttemptMean.restart_stage_attempt_mean n r M₁ M₂ o₁ o₂ p hn
          hfull hr h₁ h₂ (a + 1) hj pref history i.val i.isLt (hq i) (hw i)
        simp_rw [prefix_stage_attempts_eq history]
        exact hm
      have hcomparison :
          (∑ bits : List.Vector Bool t, (prefixAttemptCost history bits.val : ℝ)) /
            (2 : ℝ) ^ t ≤ (s.τ : ℝ) * ∑ i : Fin (a + 1), budget i := by
        rw [prefix_stage_attempt_mean_sum history t, Finset.mul_sum]
        exact Finset.sum_le_sum fun i _ => hstage i
      have htotal :
          (∑ bits : List.Vector Bool t, (prefixAttemptCost history bits.val : ℝ)) /
            (2 : ℝ) ^ t ≤ 20 * (n : ℝ) ^ 2 * (s.L : ℝ) * (s.τ : ℝ) := by
        apply hcomparison.trans
        calc
          (s.τ : ℝ) * (∑ i : Fin (a + 1), budget i) ≤
              (s.τ : ℝ) * ∑ _i : Fin (a + 1), 20 * (n : ℝ) ^ 2 :=
            mul_le_mul_of_nonneg_left (Finset.sum_le_sum fun i _ => hbudget i) (by positivity)
          _ = 20 * (n : ℝ) ^ 2 * ((a + 1 : ℕ) : ℝ) * (s.τ : ℝ) := by simp; ring
          _ ≤ 20 * (n : ℝ) ^ 2 * (s.L : ℝ) * (s.τ : ℝ) := by
            have hjreal : ((a + 1 : ℕ) : ℝ) ≤ (s.L : ℝ) := by exact_mod_cast hj.le
            exact mul_le_mul_of_nonneg_right
              (mul_le_mul_of_nonneg_left hjreal (by positivity)) (by positivity)
      apply (Rat.cast_le (K := ℝ)).mp
      push_cast
      exact htotal
