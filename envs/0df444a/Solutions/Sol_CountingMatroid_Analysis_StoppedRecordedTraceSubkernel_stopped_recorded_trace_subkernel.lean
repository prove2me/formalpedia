-- Prove2me | solution 1 for CountingMatroid.Analysis.StoppedRecordedTraceSubkernel.stopped_recorded_trace_subkernel
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-10-24T16:23:00.8731+00:00
-- url     : https://prove2.me/submissions/7e885bf9-22df-45f8-8e35-3871649927df

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
import Definitions.Def_CountingMatroidSupport_Probability_Bilinear
import Definitions.Def_CountingMatroidSupport_Probability_FinDist
import Definitions.Def_CountingMatroidSupport_Probability_FinDistFunctional
import Definitions.Def_CountingMatroid_Analysis_AnnealingPartitionDrift
import Definitions.Def_CountingMatroid_Analysis_BalancedCliqueFlow
import Definitions.Def_CountingMatroid_Analysis_BoundedRunPhase
import Definitions.Def_CountingMatroid_Analysis_BoundedRunPhaseHistory
import Definitions.Def_CountingMatroid_Analysis_BoundedRunPhaseWork
import Definitions.Def_CountingMatroid_Analysis_BoundedUniformReplay
import Definitions.Def_CountingMatroid_Analysis_ChainStepIntervalReplay
import Definitions.Def_CountingMatroid_Analysis_ConditionalDefectCoefficients
import Definitions.Def_CountingMatroid_Analysis_ConditionalDefectExtractionCoefficients
import Definitions.Def_CountingMatroid_Analysis_ConditionalDefectQuadratics
import Definitions.Def_CountingMatroid_Analysis_ConditionalSelectedStateSum
import Definitions.Def_CountingMatroid_Analysis_ConditionalTransversalSlots
import Definitions.Def_CountingMatroid_Analysis_ConditionalTransversalSplitTransport
import Definitions.Def_CountingMatroid_Analysis_ConditionalVarianceTree
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
import Definitions.Def_CountingMatroid_Analysis_QuadraticNonpositiveHyperplane
import Definitions.Def_CountingMatroid_Analysis_RankWeightQuadraticSignature
import Definitions.Def_CountingMatroid_Analysis_RankWeightSupportExchange
import Definitions.Def_CountingMatroid_Analysis_RationalHeight
import Definitions.Def_CountingMatroid_Analysis_RecordedObservationTrajectory
import Definitions.Def_CountingMatroid_Analysis_RecordedTraceContinuationBound
import Definitions.Def_CountingMatroid_Analysis_RelativeObservationBounds
import Definitions.Def_CountingMatroid_Analysis_ScheduleConfidence
import Definitions.Def_CountingMatroid_Analysis_ScheduleOpeningCost
import Definitions.Def_CountingMatroid_Analysis_ScheduleThermalSetupCost
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
import Theorems.Thm_CountingMatroid_Analysis_FiniteStoppedFiberMass_stopped_fiber_bound
import Theorems.Thm_CountingMatroid_Analysis_ObservePhaseIntervalReplay_observePhase_success_interval
import Theorems.Thm_CountingMatroid_Analysis_RecordedObservationTrajectory_recorded_trace_projection
import Theorems.Thm_CountingMatroid_Analysis_StoppedRecordedTraceSubkernel_ideal_prefix_mass
import Theorems.Thm_CountingMatroid_Analysis_StoppedRecordedTraceSubkernel_phase_trace_bound

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
namespace CountingMatroid.Analysis.StoppedRecordedTraceSubkernel
end CountingMatroid.Analysis.StoppedRecordedTraceSubkernel
namespace CountingMatroid.Analysis.ObservePhaseIntervalReplay
end CountingMatroid.Analysis.ObservePhaseIntervalReplay
section


set_option autoImplicit false

/-!
Record the actual states visited by the operational observation loop. The trace
retains its rejection-draw aborts and uses the supplied tape and cursors. Its
observable sums agree exactly with the program's counters and numerator sum.
This deterministic construction supplies the sample space for a subsequent
comparison with the ideal path law; it does not assert that law comparison.
-/
namespace CountingMatroid.Analysis.RecordedObservationTrajectory

open CountingMatroid.Model CountingMatroid.Model.Operations CountingMatroid.Program
open CountingMatroid.Analysis.PhaseObservationExperiment
open CountingMatroid.Analysis.StationaryObservableMSE



















/-- INTERNAL: Projecting the recorded full phase gives the original
observePhase output, including its abort value.
TEXLINE: main.tex:1181-1187 -/
theorem recorded_trace_observePhase {n : ℕ} (r : ℕ)
    (o₁ o₂ : IndependenceOracle n) (tape : ℕ → Bool) (s : AnnealingSchedule)
    (q : ℚ) (weights : Multipliers n) (start : PairedSet n × ℕ) :
    (observePhaseTrace r o₁ o₂ tape s q weights start).map Prod.fst =
      (observePhase r o₁ o₂ tape s q weights start).val := by
  exact recorded_trace_projection r o₁ o₂ tape s q weights
    (List.range s.observations) _



end CountingMatroid.Analysis.RecordedObservationTrajectory

/-! ### Run record
Newest first. History, not instruction — what this file claims is above.

* 2026-10-08 · proved · constructed the operational recorded trace, proved exact charged-fold projection and all accumulator sums, and recovered a state list and every empirical mean from each successful observation output.
-/

end

section


set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

/-! Finite uniform tape disintegration at a successful fixed endpoint cursor. -/
namespace CountingMatroid.Analysis.FiniteStoppedFiberMass









/-- INTERNAL: Appending fresh bits leaves every bit in the old prefix fixed. -/
theorem finiteTape_append_agree (head tail₁ tail₂ : List Bool) (i : ℕ)
    (hi : i < head.length) :
    finiteTape (head ++ tail₁) i = finiteTape (head ++ tail₂) i := by
  unfold finiteTape
  rw [List.getElem?_append_left hi, List.getElem?_append_left hi]





/-- INTERNAL: Inclusion of finite-tape events increases their mass. -/
theorem fairMass_mono (head : List Bool) (t : ℕ) (E F : (ℕ → Bool) → Prop)
    (h : ∀ bits : List.Vector Bool t,
      E (finiteTape (head ++ bits.val)) → F (finiteTape (head ++ bits.val))) :
    fairMass head t E ≤ fairMass head t F := by
  classical
  apply Finset.sum_le_sum
  intro bits _
  by_cases he : E (finiteTape (head ++ bits.val))
  · simp only [he, h bits he, if_true, le_refl]
  · simp only [he, if_false]
    split_ifs <;> positivity





end CountingMatroid.Analysis.FiniteStoppedFiberMass

end

section


set_option autoImplicit false

/-! Covered finite-tape bounds for the transition part of recorded observations. -/
namespace CountingMatroid.Analysis.RecordedTraceContinuationBound
open CountingMatroid.Model CountingMatroid.Program
open CountingMatroid.Analysis.RecordedObservationTrajectory
open CountingMatroid.Analysis.FiniteStoppedFiberMass









/-- INTERNAL: Every specified continuation has nonnegative ideal weight. -/
theorem continuationWeight_nonneg {α : Type} [Fintype α]
    (P : Arlib.MarkovChains.FinChain α) (current : α) (states : List α) :
    0 ≤ continuationWeight P current states := by
  induction states generalizing current with
  | nil => exact zero_le_one
  | cons a states ih => exact mul_nonneg (P.coe_nonneg _ _) (ih a)



end CountingMatroid.Analysis.RecordedTraceContinuationBound

end
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

/-!
Stopped-prefix composition for recorded observations. The initializer is an
arbitrary successful interval-local operation returning a transversal and an
adaptive cursor. Coverage is an explicit deterministic hypothesis; the
one-step subkernel bound is an explicit stochastic hypothesis. These separate
inputs keep the composition independent of the schedule's bit budget and of
warm restart estimates. Successful initializer fibers are disintegrated at
their ending cursor, covered transition continuations are bounded by their
ideal products, and the unused last ideal transition is summed out. Zero
observations and overrun initializers are handled separately.
-/
namespace CountingMatroid.Analysis.StoppedRecordedTraceSubkernel
end CountingMatroid.Analysis.StoppedRecordedTraceSubkernel
open CountingMatroid CountingMatroid.Analysis CountingMatroid.Analysis.StoppedRecordedTraceSubkernel

open CountingMatroid.Model CountingMatroid.Model.Operations CountingMatroid.Program
open CountingMatroid.Analysis.RecordedObservationTrajectory
open CountingMatroid.Analysis.FiniteStoppedFiberMass
open CountingMatroid.Analysis.RecordedTraceContinuationBound

/-- INTERNAL: Compose covered one-step subkernels after an interval-local
initializer without normalizing its successful endpoint fibers. All successful
completed traces fit in the given fair suffix, so no defaulted bits are counted
as fresh randomness. The last ideal transition is summed out.
TEXLINE: main.tex:1181-1187,1207-1212,1392-1421 -/
theorem solution {n : ℕ} (r : ℕ)
    (o₁ o₂ : IndependenceOracle n) (s : AnnealingSchedule)
    (q : ℚ) (weights : Multipliers n) (head : List Bool) (t : ℕ)
    (initialRun : (ℕ → Bool) → Option (PairedSet n × ℕ))
    (hreplay : ChainStepIntervalReplay.SuccessReplay initialRun Prod.snd head.length)
    (htrans : ∀ tape start, initialRun tape = some start →
      (classifyState start.1).val = .transversal)
    (hcovered : ∀ (suffix : List.Vector Bool t) start observed recorded,
      initialRun (fun i => ((head ++ suffix.val)[i]?).getD false) = some start →
      observePhaseTrace r o₁ o₂ (fun i => ((head ++ suffix.val)[i]?).getD false)
        s q weights start = some (observed, recorded) →
      observed.bitCursor ≤ head.length + t)
    (P : Arlib.MarkovChains.FinChain (PairedSet n))
    (hstep : by
      classical
      exact ∀ (pref : List Bool) (u : ℕ) (state next : PairedSet n),
        state.card = n → (classifyState state).val ≠ .invalid →
        (∑ suffix : List.Vector Bool u,
          if ∃ stop : ℕ, stop ≤ pref.length + u ∧
            (chainStep r o₁ o₂ (fun i => ((pref ++ suffix.val)[i]?).getD false)
              s.drawTrials q weights state pref.length).val = some (next, stop)
          then 1 / (2 : ℝ) ^ u else 0) ≤ P state next)
    (start : PairedSet n × ℕ)
    (states : List.Vector (PairedSet n) s.observations) :
    by
    classical
    exact (∑ suffix : List.Vector Bool t,
      if initialRun (fun i => ((head ++ suffix.val)[i]?).getD false) = some start ∧
        ∃ observed : ObservationCursor n,
          observePhaseTrace r o₁ o₂ (fun i => ((head ++ suffix.val)[i]?).getD false)
            s q weights start = some (observed, states.val)
      then 1 / (2 : ℝ) ^ t else 0) ≤
    (∑ suffix : List.Vector Bool t,
      if initialRun (fun i => ((head ++ suffix.val)[i]?).getD false) = some start
      then 1 / (2 : ℝ) ^ t else 0) *
    ∑ path : Fin (s.observations + 1) → PairedSet n,
      if List.ofFn (fun i : Fin s.observations => path i.castSucc) = states.val ∧
        start.1 = path 0
      then ∏ i : Fin s.observations, P (path i.castSucc) (path i.succ) else 0 := by
  classical
  by_cases hzero : s.observations = 0
  · have hstates : states.val = [] :=
      List.length_eq_zero_iff.mp (states.2.trans hzero)
    have hpath : (∑ path : Fin (s.observations + 1) → PairedSet n,
        if List.ofFn (fun i : Fin s.observations => path i.castSucc) = states.val ∧
          start.1 = path 0
        then ∏ i : Fin s.observations, P (path i.castSucc) (path i.succ) else 0) = 1 := by
      simp only [hzero, hstates, List.ofFn_zero, true_and]
      rw [Finset.sum_eq_single (fun _ => start.1)]
      · simp [hzero]
      · intro path _ hne
        apply if_neg
        intro heq
        apply hne
        funext i
        have hi : i = 0 := Fin.ext (by
          have hi := i.isLt
          simp only [Fin.val_zero]
          omega)
        rw [hi, ← heq]
      · simp
    rw [hpath, mul_one]
    apply Finset.sum_le_sum
    intro suffix _
    simp [observePhaseTrace, hzero, recordedObservationTrace, hstates]
  · by_cases hcursor : start.2 ≤ head.length + t
    · cases hstates : states.val with
      | nil =>
        exact False.elim (hzero (by simpa only [hstates, List.length_nil] using states.2.symm))
      | cons a rest =>
        have hobs : s.observations = rest.length + 1 := by
          simpa only [hstates, List.length_cons] using states.2.symm
        rw [ideal_prefix_mass P s.observations (a :: rest)
          (by simpa only [List.length_cons] using hobs.symm) start.1]
        dsimp only
        suffices hmass : fairMass head t (fun tape => initialRun tape = some start ∧
          ∃ observed : ObservationCursor n,
            observePhaseTrace r o₁ o₂ tape s q weights start = some (observed, a :: rest)) ≤
          fairMass head t (fun tape => initialRun tape = some start) *
            (if start.1 = a then continuationWeight P a rest else 0) by
          delta fairMass finiteTape at hmass
          convert hmass using 1
          · apply Finset.sum_congr rfl
            intro bits _
            split_ifs <;> rfl
          · congr 1
            apply Finset.sum_congr rfl
            intro bits _
            split_ifs <;> rfl
        by_cases hstart : head.length ≤ start.2
        · apply stopped_fiber_bound head t initialRun Prod.snd hreplay start hstart hcursor
          · by_cases ha : start.1 = a
            · simpa only [if_pos ha] using continuationWeight_nonneg P a rest
            · simp only [if_neg ha, le_refl]
          · intro pref hinit
            have hpref : (head ++ pref.val).length = start.2 := by
              simp only [List.length_append, pref.2]
              omega
            have hbudget : (head ++ pref.val).length + (t - (start.2-head.length)) =
                head.length + t := by
              rw [hpref]
              omega
            have hvalid : (classifyState start.1).val ≠ .invalid := by
              rw [htrans (finiteTape (head ++ pref.val)) start hinit]
              intro heq
              cases heq
            have hcover : ∀ tail : List.Vector Bool (t - (start.2-head.length)),
                (∃ observed : ObservationCursor n,
                  observePhaseTrace r o₁ o₂ (finiteTape ((head ++ pref.val) ++ tail.val))
                    s q weights start = some (observed, a :: rest)) →
                ∃ observed : ObservationCursor n,
                  observed.bitCursor ≤ (head ++ pref.val).length +
                    (t - (start.2-head.length)) ∧
                  observePhaseTrace r o₁ o₂ (finiteTape ((head ++ pref.val) ++ tail.val))
                    s q weights start = some (observed, a :: rest) := by
              intro tail
              rintro ⟨observed, htrace⟩
              let suffix : List.Vector Bool t := ⟨pref.val ++ tail.val, by
                simp only [List.length_append, pref.2, tail.2]
                omega⟩
              have hinitFull : initialRun
                  (finiteTape ((head ++ pref.val) ++ tail.val)) = some start :=
                (hreplay (finiteTape (head ++ pref.val)) start hinit).2 _ (by
                  intro i _ hi
                  have hagree := finiteTape_append_agree (head ++ pref.val) [] tail.val i
                    (by rw [hpref]; exact hi)
                  simpa only [List.append_nil] using hagree)
              delta finiteTape at hinitFull htrace
              have hc := hcovered suffix start observed states.val
                (by simpa only [suffix, List.append_assoc] using hinitFull)
                (by simpa only [suffix, List.append_assoc, hstates] using htrace)
              exact ⟨observed, by rw [hbudget]; exact hc, htrace⟩
            exact (fairMass_mono _ _ _ _ hcover).trans
              (phase_trace_bound r o₁ o₂ s q weights P (by
                intro pref u state next hc hv
                delta fairMass finiteTape
                convert hstep pref u state next hc hv using 1
                apply Finset.sum_congr rfl
                intro bits _
                split_ifs <;> rfl) a rest hobs
                (head ++ pref.val) (t - (start.2-head.length)) start hpref.symm hvalid)
        · have hnone : ∀ tape, initialRun tape ≠ some start := by
            intro tape hinit
            exact hstart (hreplay tape start hinit).1
          unfold fairMass
          simp only [hnone, false_and, if_false, Finset.sum_const_zero, zero_mul, le_refl]
    · have hevent : ∀ suffix : List.Vector Bool t,
          ¬ (initialRun (fun i => ((head ++ suffix.val)[i]?).getD false) = some start ∧
            ∃ observed : ObservationCursor n,
              observePhaseTrace r o₁ o₂ (fun i => ((head ++ suffix.val)[i]?).getD false)
                s q weights start = some (observed, states.val)) := by
        intro suffix
        rintro ⟨hinit, observed, htrace⟩
        have hproj := recorded_trace_observePhase r o₁ o₂
          (fun i => ((head ++ suffix.val)[i]?).getD false) s q weights start
        rw [htrace] at hproj
        have hmono := (ObservePhaseIntervalReplay.observePhase_success_interval
          r o₁ o₂ s q weights start
          (fun i => ((head ++ suffix.val)[i]?).getD false) observed hproj.symm).1
        exact hcursor (hmono.trans (hcovered suffix start observed states.val hinit htrace))
      simp only [hevent, if_false, Finset.sum_const_zero]
      apply mul_nonneg
      · apply Finset.sum_nonneg
        intro suffix _
        split_ifs <;> positivity
      · apply Finset.sum_nonneg
        intro path _
        split_ifs
        · exact Finset.prod_nonneg (fun i _ => P.coe_nonneg _ _)
        · exact le_rfl
