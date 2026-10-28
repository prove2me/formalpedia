-- Prove2me | solution 1 for CountingMatroid.Analysis.CappedRestartFinalTraceDomination.capped_restart_final_trace_domination
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-10-24T16:38:32.569171+00:00
-- url     : https://prove2.me/submissions/167b6d6c-87eb-4548-bb5a-ce790b510079

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
import Definitions.Def_CountingMatroid_Analysis_RestartPhaseBitCoverage
import Definitions.Def_CountingMatroid_Analysis_RestartSuffixMassDefinition
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
import Definitions.Def_CountingMatroid_Analysis_ThreePairSignatureSchur
import Definitions.Def_CountingMatroid_Analysis_TransversalClassPartition
import Definitions.Def_CountingMatroid_Analysis_TransversalEventMean
import Definitions.Def_CountingMatroid_Analysis_TransversalPartition
import Definitions.Def_CountingMatroid_Analysis_TransversalProjection
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
import Theorems.Thm_CountingMatroid_Analysis_CappedRestartFinalTraceDomination_restart_final_stage_event_iff
import Theorems.Thm_CountingMatroid_Analysis_CappedRestartFinalTraceDomination_restart_phase_cursor_projection
import Theorems.Thm_CountingMatroid_Analysis_CappedRestartFinalTraceDomination_restart_phase_cursor_success_interval
import Theorems.Thm_CountingMatroid_Analysis_CappedTraceIterationSubkernel_covered_trace_fold_bound
import Theorems.Thm_CountingMatroid_Analysis_ChainStepIntervalReplay_foldl_successReplay
import Theorems.Thm_CountingMatroid_Analysis_CoveredChainStepSubkernel_covered_chain_step_subkernel
import Theorems.Thm_CountingMatroid_Analysis_FiniteStoppedKernelBind_stopped_kernel_bind_bound
import Theorems.Thm_CountingMatroid_Analysis_RecordedTraceContinuationBound_classified_card
import Theorems.Thm_CountingMatroid_Analysis_RestartPhaseBitCoverage_restart_phase_cursor_le_block
import Theorems.Thm_CountingMatroid_Analysis_RestartPhaseTransversal_restartPhase_transversal
import Theorems.Thm_CountingMatroid_Analysis_SuccessfulPrefixAbortBound_successful_prefix_has_good_cursor
import Theorems.Thm_CountingMatroid_Analysis_SuccessfulPrefixRestartEndpointMass_restart_suffix_mass_subprobability
import Theorems.Thm_CountingMatroid_Analysis_TraceReturnIntervalReplay_traceReturn_success_interval

namespace CountingMatroid.Meta
end CountingMatroid.Meta
namespace Arlib
end Arlib
namespace CountingMatroid.Analysis.ChainStepNoninvalid
end CountingMatroid.Analysis.ChainStepNoninvalid
namespace CountingMatroid.Analysis.IdealChainNonnegDefinite
end CountingMatroid.Analysis.IdealChainNonnegDefinite
namespace CountingMatroid.Analysis.ExchangeProposalGeometry
end CountingMatroid.Analysis.ExchangeProposalGeometry
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
namespace CountingMatroid.Interface
end CountingMatroid.Interface
namespace CountingMatroid.Analysis.TransversalRankBridge
end CountingMatroid.Analysis.TransversalRankBridge
namespace CountingMatroid.Analysis.GreedyRankCorrect
end CountingMatroid.Analysis.GreedyRankCorrect
namespace CountingMatroid.Analysis.ObservableEnergyDual
end CountingMatroid.Analysis.ObservableEnergyDual
namespace CountingMatroid.Analysis.TypeMassLowerBounds
end CountingMatroid.Analysis.TypeMassLowerBounds
namespace CountingMatroid.Analysis.StationaryCovarianceSum
end CountingMatroid.Analysis.StationaryCovarianceSum
namespace CountingMatroid.Analysis.FinitePhaseEstimationBound
end CountingMatroid.Analysis.FinitePhaseEstimationBound
namespace CountingMatroid.Analysis.FiniteObservationMarkov
end CountingMatroid.Analysis.FiniteObservationMarkov
namespace CountingMatroid.Analysis.FiniteTapePrefixBound
end CountingMatroid.Analysis.FiniteTapePrefixBound
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
namespace CountingMatroid.Analysis.ObservationRoundDrawSites
end CountingMatroid.Analysis.ObservationRoundDrawSites
namespace CountingMatroid.Analysis.ClassifiedStateSelection
end CountingMatroid.Analysis.ClassifiedStateSelection
namespace CountingMatroid.Analysis.InitialRestartLaw
end CountingMatroid.Analysis.InitialRestartLaw
namespace CountingMatroid.Analysis.BoundedUniformSubkernel
end CountingMatroid.Analysis.BoundedUniformSubkernel
namespace CountingMatroid.Analysis.BoundedUniformSuccessWords
end CountingMatroid.Analysis.BoundedUniformSuccessWords
namespace CountingMatroid.Analysis.SuccessfulPrefixAbortBound
end CountingMatroid.Analysis.SuccessfulPrefixAbortBound
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
namespace CountingMatroid.Analysis.RestartPhaseTransversal
end CountingMatroid.Analysis.RestartPhaseTransversal
namespace CountingMatroid.Analysis.RestartPhaseIntervalReplay
end CountingMatroid.Analysis.RestartPhaseIntervalReplay
namespace CountingMatroid.Analysis.TraceReturnIntervalReplay
end CountingMatroid.Analysis.TraceReturnIntervalReplay
namespace CountingMatroid.Analysis.FiniteStoppedKernelBind
end CountingMatroid.Analysis.FiniteStoppedKernelBind
namespace Arlib.MarkovChains
end Arlib.MarkovChains
namespace Arlib.MarkovChains.FinChain
end Arlib.MarkovChains.FinChain
namespace Arlib.MarkovChains.FinKernel
end Arlib.MarkovChains.FinKernel
namespace Arlib.Probability
end Arlib.Probability
namespace Arlib.Probability.FinDist
end Arlib.Probability.FinDist
namespace Arlib.Probability.FinKernel
end Arlib.Probability.FinKernel
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

/-- INTERNAL: The final stage retains the interval replay of all its positive
time returns, including the shared attempt counter in the result.
TEXLINE: main.tex:1163-1176,1392-1421 -/
theorem restart_stage_success_interval {n : ℕ} (r : ℕ)
    (o₁ o₂ : IndependenceOracle n) (s : AnnealingSchedule)
    (tables : LearnedWeights n) (index : ℕ) (current : RestartCursor n) :
    ChainStepIntervalReplay.SuccessReplay
      (fun tape => (restart_stage r o₁ o₂ tape s tables index (some current)).val)
      RestartCursor.bitCursor current.bitCursor := by
  unfold restart_stage
  simp only [Arlib.Computation.Charged.val_bind, Arlib.Computation.Charged.repeatFor]
  apply ChainStepIntervalReplay.foldl_successReplay
  · intro tape index
    rfl
  · intro acc index
    exact TraceReturnIntervalReplay.traceReturn_success_interval r o₁ o₂ s _ _ acc



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



/-- INTERNAL: A stage containing zero trace transitions retains the whole
cursor, including its shared attempt count.
TEXLINE: main.tex:1163-1176 -/
theorem restart_stage_zero_trace {n : ℕ} (r : ℕ)
    (o₁ o₂ : IndependenceOracle n) (tape : ℕ → Bool)
    (s : AnnealingSchedule) (tables : LearnedWeights n) (index : ℕ)
    (current : Option (RestartCursor n)) (hτ : s.τ = 0) :
    (restart_stage r o₁ o₂ tape s tables index current).val = current := by
  cases current <;>
    simp only [restart_stage, Arlib.Computation.Charged.val_bind, hτ,
      Arlib.Computation.Charged.repeatFor, List.range_zero,
      Arlib.Computation.Charged.val_foldl_nil, Arlib.Computation.Charged.val_pure]

/-- INTERNAL: If every stage has zero trace transitions, the restart is its
single fresh transversal scan, independently of the number of stages.
TEXLINE: main.tex:1163-1176 -/
theorem restart_phase_cursor_zero_trace {n : ℕ} (r : ℕ)
    (o₁ o₂ : IndependenceOracle n) (tape : ℕ → Bool)
    (s : AnnealingSchedule) (tables : LearnedWeights n) (j cursor : ℕ)
    (hτ : s.τ = 0) :
    restart_phase_cursor r o₁ o₂ tape s tables j cursor =
      some ⟨(freshTransversal n tape cursor).val.1,
        (freshTransversal n tape cursor).val.2, 0⟩ := by
  induction j with
  | zero => rfl
  | succ j ih =>
      rw [restart_phase_cursor_succ, restart_stage_zero_trace r o₁ o₂ tape s tables j _ hτ,
        ih]



/-- INTERNAL: Expose the actual final-stage event before any probability
comparison. The preceding internal restart retains its remaining global cap.
TEXLINE: main.tex:1163-1176 -/
theorem restart_suffix_mass_final_stage {n : ℕ} (r : ℕ)
    (o₁ o₂ : IndependenceOracle n) (s : AnnealingSchedule) (j : ℕ)
    (hj : 0 < j) (current : AnnealingCursor n) (pref : List Bool) (t : ℕ)
    (state : PairedSet n) :
    restartSuffixMass r o₁ o₂ s j current pref t state =
      ∑ suffix : List.Vector Bool t,
        if ((restart_stage r o₁ o₂
          (fun i => ((pref ++ suffix.val)[i]?).getD false) s current.tables (j - 1)
          (restart_phase_cursor r o₁ o₂
            (fun i => ((pref ++ suffix.val)[i]?).getD false) s current.tables (j - 1)
            current.bitCursor)).val).map RestartCursor.state = some state
        then 1 / (2 : ℝ) ^ t else 0 := by
  classical
  unfold restartSuffixMass
  apply Finset.sum_congr rfl
  intro suffix _
  have hsplit := restart_phase_cursor_succ r o₁ o₂
    (fun i => ((pref ++ suffix.val)[i]?).getD false) s current.tables (j - 1)
    current.bitCursor
  rw [Nat.sub_add_cancel (Nat.succ_le_of_lt hj)] at hsplit
  rw [restart_phase_cursor_projection, hsplit, Option.map_map]
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
end CountingMatroid.Analysis.CappedRestartFinalTraceDomination
open CountingMatroid CountingMatroid.Analysis CountingMatroid.Analysis.CappedRestartFinalTraceDomination

open CountingMatroid.Model CountingMatroid.Program
open CountingMatroid.Analysis.PhaseObservationExperiment

/-- INTERNAL: Dominate the final operational restart stage by iterated
capped ideal positive-time returns, retaining the actual previous-stage mass.
The cap is granted afresh per ideal return, so no successful operational
restart is removed by the reference subkernel.
TEXLINE: main.tex:1163-1176,1207-1212,1392-1421 -/
theorem solution (n r : ℕ)
    (M₁ M₂ : Matroid (Fin n)) (o₁ o₂ : IndependenceOracle n)
    (p : InputParams) (hn : 0 < n) (hfull : FullGround M₁ M₂)
    (hr : CommonRank r M₁ M₂) (h₁ : ExactOracle M₁ o₁)
    (h₂ : ExactOracle M₂ o₂) (hpositive : 0 < commonBaseCount M₁ M₂)
    (j : ℕ) (hj : j < (CountingMatroid.Interface.Pseudocode.setup n p).L)
    (hjpos : 0 < j) (pref : List Bool)
    (hprefix : SuccessfulPhasePrefix n r o₁ o₂ p j pref)
    (current : AnnealingCursor n) (hw : ∀ a, 0 < current.currentWeights a)
    (hgood : FirstPhaseFailure.GoodStoredMultipliers r o₁ o₂
      (CountingMatroid.Interface.Pseudocode.setup n p) j current)
    (htable : ∀ a, 0 < current.tables j a)
    (hfixed : ∀ suffix : List.Vector Bool
        (CountingMatroid.Model.Run.blockLength n r p - pref.length),
      BoundedRunPhaseHistory.phaseHistory r o₁ o₂
        (fun i => ((pref ++ suffix.val)[i]?).getD false)
        (CountingMatroid.Interface.Pseudocode.setup n p) j = some current)
    (state : PairedSet n) :
    let s := CountingMatroid.Interface.Pseudocode.setup n p
    let t := CountingMatroid.Model.Run.blockLength n r p - pref.length
    let hq := pow_pos (AnnealingPartitionDrift.schedule_power_lower n p hn).1 j
    let P := IdealExchangeChain.idealChain r o₁ o₂ (s.ρ ^ j)
      (current.tables j) hn hq htable
    let A := Finset.univ.filter (fun x : PairedSet n => (classifyState x).val = .transversal)
    restartSuffixMass r o₁ o₂ s j current pref t state ≤
      ∑ x, restartSuffixMass r o₁ o₂ s (j - 1) current pref t x *
        (PositiveTimeTraceKernel.iterate
          (PositiveTimeTraceKernel.returnWithin P A s.restartCap) s.τ).entry x state := by
  classical
  dsimp only
  let s := CountingMatroid.Interface.Pseudocode.setup n p
  let t := CountingMatroid.Model.Run.blockLength n r p - pref.length
  by_cases hτ : s.τ = 0
  · have hmass : restartSuffixMass r o₁ o₂ s j current pref t state =
        restartSuffixMass r o₁ o₂ s (j - 1) current pref t state := by
      unfold restartSuffixMass
      apply Finset.sum_congr rfl
      intro suffix _
      rw [restart_phase_cursor_projection, restart_phase_cursor_projection,
        restart_phase_cursor_zero_trace r o₁ o₂ _ s current.tables j current.bitCursor hτ,
        restart_phase_cursor_zero_trace r o₁ o₂ _ s current.tables (j - 1)
          current.bitCursor hτ]
    change restartSuffixMass r o₁ o₂ s j current pref t state ≤ _
    simp only [show (CountingMatroid.Interface.Pseudocode.setup n p).τ = 0 from hτ,
      PositiveTimeTraceKernel.iterate, PositiveTimeTraceKernel.identity]
    simpa only [mul_ite, mul_one, mul_zero, Finset.sum_ite_eq', Finset.mem_univ,
      if_true] using hmass.le
  have hν := SuccessfulPrefixRestartEndpointMass.restart_suffix_mass_subprobability
    r o₁ o₂ s (j - 1) current pref t
  change (∀ x, 0 ≤ restartSuffixMass r o₁ o₂ s (j - 1) current pref t x) ∧
    (∑ x, restartSuffixMass r o₁ o₂ s (j - 1) current pref t x) ≤ 1 ∧
    (∀ x, (classifyState x).val ≠ .transversal →
      restartSuffixMass r o₁ o₂ s (j - 1) current pref t x = 0) at hν
  by_cases htrans : (classifyState state).val = .transversal
  case neg =>
    have hzero := (SuccessfulPrefixRestartEndpointMass.restart_suffix_mass_subprobability
        r o₁ o₂ s j current pref t).2.2 state htrans
    change restartSuffixMass r o₁ o₂ s j current pref t state = 0 at hzero
    change restartSuffixMass r o₁ o₂ s j current pref t state ≤ _
    rw [hzero]
    apply Finset.sum_nonneg
    intro x _
    exact mul_nonneg (hν.1 x) (PositiveTimeTraceKernel.Subkernel.nonneg _ x state)
  change restartSuffixMass r o₁ o₂ s j current pref t state ≤ _
  let m := CountingMatroid.Model.Run.blockLength n r p
  let q := s.ρ ^ j
  have hq : 0 < q := pow_pos (AnnealingPartitionDrift.schedule_power_lower n p hn).1 j
  let P := IdealExchangeChain.idealChain r o₁ o₂ q (current.tables j) hn hq htable
  let A := Finset.univ.filter (fun x : PairedSet n => (classifyState x).val = .transversal)
  let K := PositiveTimeTraceKernel.iterate
    (PositiveTimeTraceKernel.returnWithin P A s.restartCap) s.τ
  let f := fun tape : ℕ → Bool =>
    restart_phase_cursor r o₁ o₂ tape s current.tables (j-1) current.bitCursor
  let E := fun tape (middle : RestartCursor n) => ∃ out : RestartCursor n,
    out.bitCursor ≤ pref.length+t ∧
    (restart_stage r o₁ o₂ tape s current.tables (j-1) (some middle)).val = some out ∧
    out.state = state
  obtain ⟨bits, original, hbits, _, horiginal, _, hpref, hprefLength⟩ :=
    SuccessfulPrefixAbortBound.successful_prefix_has_good_cursor n r o₁ o₂ p j hj pref hprefix
  have hp : pref <+: bits := hpref ▸ List.take_prefix _ _
  have hconcat : pref ++ bits.drop pref.length = bits := (List.prefix_append_drop hp).symm
  let originalSuffix : List.Vector Bool t :=
    ⟨bits.drop pref.length, by simpa only [t, m, List.length_drop, hbits]⟩
  have hsame := hfixed originalSuffix
  change BoundedRunPhaseHistory.phaseHistory r o₁ o₂
    (fun i => ((pref ++ bits.drop pref.length)[i]?).getD false) s j = some current at hsame
  rw [hconcat, horiginal] at hsame
  have heq : original = current := Option.some.inj hsame
  have hstart : pref.length ≤ current.bitCursor := by
    rw [hprefLength, ← heq]
    exact Nat.min_le_left _ _
  have hlen : pref.length ≤ m := by
    rw [hprefLength]
    exact Nat.min_le_right _ _
  have htotal : pref.length+t = m := Nat.add_sub_of_le hlen
  have hf : ChainStepIntervalReplay.SuccessReplay f RestartCursor.bitCursor pref.length := by
    intro tape out hr
    have hi := restart_phase_cursor_success_interval r o₁ o₂ s current.tables
      (j-1) current.bitCursor tape out hr
    exact ⟨hstart.trans hi.1, fun other hagree =>
      hi.2 other (fun i hlo hhi => hagree i (hstart.trans hlo) hhi)⟩
  have htransStart : ∀ tape middle, f tape = some middle →
      (classifyState middle.state).val = .transversal := by
    intro tape middle hr
    have hp := restart_phase_cursor_projection r o₁ o₂ tape s current.tables (j-1)
      current.bitCursor
    dsimp only [f] at hr
    rw [hr] at hp
    exact RestartPhaseTransversal.restartPhase_transversal r o₁ o₂ tape s current.tables
      (j-1) current.bitCursor (middle.state,middle.bitCursor) hp
  have hstep : ∀ (head : List Bool) (u : ℕ) (x y : PairedSet n),
      (classifyState x).val ≠ .invalid →
      FiniteStoppedFiberMass.fairMass head u (fun tape => ∃ stop, stop ≤ head.length+u ∧
        (chainStep r o₁ o₂ tape s.drawTrials q (current.tables j) x head.length).val =
          some (y,stop)) ≤ P x y := by
    intro head u x y hv
    have hb := CoveredChainStepSubkernel.covered_chain_step_subkernel r o₁ o₂ s.drawTrials q
      (current.tables j) hn hq htable head u x y
      (RecordedTraceContinuationBound.classified_card x hv) hv
    convert hb using 1
    unfold FiniteStoppedFiberMass.fairMass CoveredChainStepSubkernel.coveredChainStepMass
    apply Finset.sum_congr rfl
    intro suffix _
    unfold FiniteStoppedFiberMass.finiteTape
    split_ifs <;> rfl
  have hleft : restartSuffixMass r o₁ o₂ s j current pref t state ≤
      FiniteStoppedFiberMass.fairMass pref t (fun tape => ∃ middle,
        f tape = some middle ∧ E tape middle) := by
    rw [restart_suffix_mass_final_stage r o₁ o₂ s j hjpos current pref t state]
    unfold FiniteStoppedFiberMass.fairMass
    apply Finset.sum_le_sum
    intro suffix _
    by_cases hs : ((restart_stage r o₁ o₂
        (FiniteStoppedFiberMass.finiteTape (pref ++ suffix.val)) s current.tables (j-1)
        (f (FiniteStoppedFiberMass.finiteTape (pref ++ suffix.val)))).val).map
          RestartCursor.state = some state
    · obtain ⟨middle, out, hm, hout, hstate, _⟩ :=
        (restart_final_stage_event_iff r o₁ o₂ _ s current.tables (j-1)
          (f _) state).mp hs
      dsimp only [f] at hm
      have hfullrun : restart_phase_cursor r o₁ o₂
          (FiniteStoppedFiberMass.finiteTape (pref ++ suffix.val)) s current.tables j
          current.bitCursor = some out := by
        have hsplit := restart_phase_cursor_succ r o₁ o₂
          (FiniteStoppedFiberMass.finiteTape (pref ++ suffix.val)) s current.tables (j-1)
          current.bitCursor
        rw [Nat.sub_add_cancel (Nat.succ_le_of_lt hjpos), hm, hout] at hsplit
        exact hsplit
      have hr : (restartPhase r o₁ o₂
          (FiniteStoppedFiberMass.finiteTape (pref ++ suffix.val)) s current.tables j
          current.bitCursor).val = some (out.state,out.bitCursor) := by
        rw [restart_phase_cursor_projection, hfullrun]
        rfl
      have hc := RestartPhaseBitCoverage.restart_phase_cursor_le_block n r o₁ o₂ p hn
        (FiniteStoppedFiberMass.finiteTape (pref ++ suffix.val)) j hj current
        (out.state,out.bitCursor) (hfixed suffix) hr
      have hevent : ∃ middle, f (FiniteStoppedFiberMass.finiteTape (pref ++ suffix.val)) =
          some middle ∧ E (FiniteStoppedFiberMass.finiteTape (pref ++ suffix.val)) middle :=
        ⟨middle, hm, out, by simpa only [htotal] using hc, hout, hstate⟩
      unfold FiniteStoppedFiberMass.finiteTape at hs hevent ⊢
      dsimp only [f] at hs hevent ⊢
      simp +instances only [hs, hevent, if_true, le_refl]
    · unfold FiniteStoppedFiberMass.finiteTape at hs ⊢
      dsimp only [f] at hs ⊢
      simp +instances only [hs, if_false]
      split_ifs <;> positivity
  have hbound := FiniteStoppedKernelBind.stopped_kernel_bind_bound pref t f
    RestartCursor.bitCursor hf E (fun middle => K.entry middle.state state)
    (fun middle => K.nonneg middle.state state) (by
      intro suffix middle _ hE
      obtain ⟨out, hc, hr, _⟩ := hE
      exact (restart_stage_success_interval r o₁ o₂ s current.tables (j-1) middle _ out hr).1.trans hc)
    (by
      intro middle hlo hhi head hm
      have hhead : (pref ++ head.val).length = middle.bitCursor := by
        simp only [List.length_append, head.2]
        omega
      have hbudget : (pref ++ head.val).length + (t-(middle.bitCursor-pref.length)) =
          pref.length+t := by rw [hhead]; omega
      have hv : (classifyState middle.state).val ≠ .invalid := by
        rw [htransStart _ middle hm]
        intro h
        cases h
      have hi := CappedTraceIterationSubkernel.covered_trace_fold_bound r o₁ o₂ s q
        (current.tables j) P hstep (List.range s.τ) (pref ++ head.val)
        (t-(middle.bitCursor-pref.length)) middle hhead.symm hv state
      have hmass : FiniteStoppedFiberMass.fairMass (pref ++ head.val)
          (t-(middle.bitCursor-pref.length)) (fun tape => E tape middle) =
          FiniteStoppedFiberMass.fairMass (pref ++ head.val)
          (t-(middle.bitCursor-pref.length)) (fun tape => ∃ out : RestartCursor n,
            out.bitCursor ≤ (pref ++ head.val).length + (t-(middle.bitCursor-pref.length)) ∧
            CappedTraceIterationSubkernel.traceFold r o₁ o₂ tape s q (current.tables j)
              (List.range s.τ) (some middle) = some out ∧ out.state = state) := by
        unfold FiniteStoppedFiberMass.fairMass
        apply Finset.sum_congr rfl
        intro tail _
        simp only [E, q, hbudget, restart_stage_eq_trace_fold,
          Nat.sub_add_cancel (Nat.succ_le_of_lt hjpos)]
      rw [hmass]
      simpa only [List.length_range] using hi)
  have hright : (∑ suffix : List.Vector Bool t, (1 / (2 : ℝ)^t) *
      ((f (FiniteStoppedFiberMass.finiteTape (pref ++ suffix.val))).map
        (fun middle => K.entry middle.state state)).getD 0) =
      ∑ x, restartSuffixMass r o₁ o₂ s (j-1) current pref t x * K.entry x state := by
    unfold restartSuffixMass
    simp only [Finset.sum_mul]
    rw [Finset.sum_comm]
    apply Finset.sum_congr rfl
    intro suffix _
    simp only [restart_phase_cursor_projection, Option.map_map]
    change (1 / (2 : ℝ)^t) *
      ((f (FiniteStoppedFiberMass.finiteTape (pref ++ suffix.val))).map
        (fun middle => K.entry middle.state state)).getD 0 =
      ∑ x : PairedSet n,
        (if (f (FiniteStoppedFiberMass.finiteTape (pref ++ suffix.val))).map
          RestartCursor.state = some x then 1 / (2 : ℝ)^t else 0) * K.entry x state
    have hterm (outcome : Option (RestartCursor n)) : (1 / (2 : ℝ)^t) *
        (outcome.map (fun middle => K.entry middle.state state)).getD 0 =
        ∑ x : PairedSet n,
          (if outcome.map RestartCursor.state = some x then 1 / (2 : ℝ)^t else 0) *
            K.entry x state := by
      cases outcome with
      | none => simp only [Option.map_none, Option.getD_none, mul_zero, reduceCtorEq,
          if_false, zero_mul, Finset.sum_const_zero]
      | some middle => simp only [Option.map_some, Option.getD_some, Option.some.injEq,
          ite_mul, zero_mul, Finset.sum_ite_eq, Finset.mem_univ, if_true]
    exact hterm (f (FiniteStoppedFiberMass.finiteTape (pref ++ suffix.val)))
  exact hleft.trans (hbound.trans_eq hright)
