-- Prove2me | solution 1 for CountingMatroid.Analysis.RecordedTraceContinuationBound.trace_continuation_bound
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-10-24T16:17:51.654006+00:00
-- url     : https://prove2.me/submissions/adfb82e6-a636-4637-8e9d-ed76c3bb1a34

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
import Theorems.Thm_CountingMatroid_Analysis_ChainStepIntervalReplay_chainStep_success_interval
import Theorems.Thm_CountingMatroid_Analysis_ChainStepIntervalReplay_foldl_successReplay
import Theorems.Thm_CountingMatroid_Analysis_ChainStepNoninvalid_chainStep_noninvalid
import Theorems.Thm_CountingMatroid_Analysis_FiniteStoppedFiberMass_stopped_next_bound
import Theorems.Thm_CountingMatroid_Analysis_RecordedObservationTrajectory_recorded_trace_projection
import Theorems.Thm_CountingMatroid_Analysis_RecordedTraceContinuationBound_attempt_success_interval
import Theorems.Thm_CountingMatroid_Analysis_RecordedTraceContinuationBound_classified_card

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
section


set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

/-! Finite uniform tape disintegration at a successful fixed endpoint cursor. -/
namespace CountingMatroid.Analysis.FiniteStoppedFiberMass















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



/-- INTERNAL: Recording changes neither the current state nor its bit cursor. -/
theorem record_preserves {n : ℕ} (r : ℕ) (o₁ o₂ : IndependenceOracle n)
    (rho : ℚ) (current next : ObservationCursor n)
    (h : (recordObservation r o₁ o₂ rho current).val = some next) :
    next.state = current.state ∧ next.bitCursor = current.bitCursor := by
  unfold recordObservation at h
  simp only [Arlib.Computation.Charged.val_bind] at h
  split at h
  · cases h
  · simp only [Arlib.Computation.Charged.val_bind] at h
    cases (Option.some.inj h).symm
    exact ⟨rfl, rfl⟩
  · simp only [Arlib.Computation.Charged.val_bind] at h
    cases (Option.some.inj h).symm
    exact ⟨rfl, rfl⟩





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

/-! Covered finite-tape bounds for the transition part of recorded observations. -/
namespace CountingMatroid.Analysis.RecordedTraceContinuationBound
end CountingMatroid.Analysis.RecordedTraceContinuationBound
open CountingMatroid CountingMatroid.Analysis CountingMatroid.Analysis.RecordedTraceContinuationBound
open CountingMatroid.Model CountingMatroid.Program
open CountingMatroid.Analysis.RecordedObservationTrajectory
open CountingMatroid.Analysis.FiniteStoppedFiberMass

/-- INTERNAL: Covered successful transition observations are dominated by the
product of their one-step subkernel bounds; recording reads no random bits.
TEXLINE: main.tex:1181-1187,1392-1421 -/
theorem solution {n : ℕ} (r : ℕ) (o₁ o₂ : IndependenceOracle n)
    (s : AnnealingSchedule) (q : ℚ) (weights : Multipliers n)
    (P : Arlib.MarkovChains.FinChain (PairedSet n))
    (hstep : ∀ (pref : List Bool) (u : ℕ) (state next : PairedSet n),
      state.card = n → (classifyState state).val ≠ .invalid →
      fairMass pref u (fun tape => ∃ stop, stop ≤ pref.length + u ∧
        (chainStep r o₁ o₂ tape s.drawTrials q weights state pref.length).val =
          some (next, stop)) ≤ P state next)
    (indices : List ℕ) (hpositive : ∀ k ∈ indices, k ≠ 0)
    (states : List (PairedSet n)) (hlen : states.length = indices.length)
    (head : List Bool) (t : ℕ) (current : ObservationCursor n)
    (hcursor : current.bitCursor = head.length)
    (hvalid : (classifyState current.state).val ≠ .invalid) :
    fairMass head t (fun tape => ∃ final : ObservationCursor n,
      final.bitCursor ≤ head.length + t ∧
      recordedObservationTrace r o₁ o₂ tape s q weights indices (some current) =
        some (final, states)) ≤ continuationWeight P current.state states := by
  classical
  induction indices generalizing states head t current with
  | nil =>
    have hs : states = [] := List.length_eq_zero_iff.mp hlen
    subst states
    change _ ≤ 1
    unfold fairMass
    apply le_trans (Finset.sum_le_sum (fun bits _ => ?_))
      (show (∑ _ : List.Vector Bool t, 1 / (2 : ℝ)^t) ≤ 1 by simp [card_vector])
    split_ifs
    · exact le_rfl
    · positivity
  | cons k ks ih =>
    cases states with
    | nil => simp at hlen
    | cons a rest =>
      have hk : k ≠ 0 := hpositive k (by simp)
      have hks : ∀ j ∈ ks, j ≠ 0 := fun j hj => hpositive j (by simp [hj])
      have hrest : rest.length = ks.length := by simpa using hlen
      let f := fun tape => (chainStep r o₁ o₂ tape s.drawTrials q weights
        current.state head.length).val
      let E := fun tape stop => ∃ middle final : ObservationCursor n,
        (recordObservation r o₁ o₂ s.ρ
          ⟨a, stop, current.counts, current.numeratorSum⟩).val = some middle ∧
        final.bitCursor ≤ head.length+t ∧
        recordedObservationTrace r o₁ o₂ tape s q weights ks (some middle) =
          some (final, rest)
      have hevent : ∀ bits : List.Vector Bool t,
        (∃ final : ObservationCursor n, final.bitCursor ≤ head.length+t ∧
          recordedObservationTrace r o₁ o₂ (finiteTape (head ++ bits.val)) s q weights
            (k::ks) (some current) = some (final, a::rest)) →
        ∃ stop, stop ≤ head.length+t ∧ f (finiteTape (head ++ bits.val)) =
          some (a,stop) ∧ E (finiteTape (head ++ bits.val)) stop := by
        intro bits
        rintro ⟨final, hfinal, ht⟩
        let tape := finiteTape (head ++ bits.val)
        change recordedObservationTrace r o₁ o₂ tape s q weights
          (k::ks) (some current) = some (final,a::rest) at ht
        have hattempt : (observationAttempt r o₁ o₂ tape s q weights k
            (some current)).val =
          (f tape).bind (fun step => (recordObservation r o₁ o₂ s.ρ
            ⟨step.1,step.2,current.counts,current.numeratorSum⟩).val) := by
          simp [observationAttempt, Model.Operations.natEqual, hk, f, hcursor,
            Arlib.Computation.Charged.val_bind]
          cases hc : (chainStep r o₁ o₂ tape s.drawTrials q weights
            current.state head.length).val with
          | none => simp
          | some step => cases step; simp
        cases hf : f tape with
        | none =>
          simp +instances only [recordedObservationTrace, Option.bind_eq_bind, hattempt, hf,
            Option.bind_none, reduceCtorEq] at ht
        | some step =>
          cases hr : (recordObservation r o₁ o₂ s.ρ
            ⟨step.1,step.2,current.counts,current.numeratorSum⟩).val with
          | none =>
            simp +instances only [recordedObservationTrace, Option.bind_eq_bind, hattempt, hf,
              Option.bind_some, hr, Option.bind_none, reduceCtorEq] at ht
          | some middle =>
            cases htail : recordedObservationTrace r o₁ o₂ tape s q weights ks
                (some middle) with
            | none =>
              simp +instances only [recordedObservationTrace, Option.bind_eq_bind, hattempt, hf,
                Option.bind_some, hr, htail, Option.bind_none, reduceCtorEq] at ht
            | some result =>
              rcases result with ⟨finished, recorded⟩
              simp +instances only [recordedObservationTrace, Option.bind_eq_bind, hattempt, hf,
                Option.bind_some, hr, htail, Option.pure_def, Option.some.injEq,
                Prod.mk.injEq, List.cons.injEq] at ht
              obtain ⟨hfinish, hstate, hrecorded⟩ := ht
              subst finished
              subst recorded
              have hp := record_preserves r o₁ o₂ s.ρ _ middle hr
              have ha : step.1 = a := hp.1.symm.trans hstate
              have hmono : middle.bitCursor ≤ final.bitCursor := by
                have hproj := recorded_trace_projection r o₁ o₂ tape s q weights ks
                  (some middle)
                rw [htail] at hproj
                have hreplay := ChainStepIntervalReplay.foldl_successReplay
                  (fun tape acc k => observationAttempt r o₁ o₂ tape s q weights k acc)
                  ObservationCursor.bitCursor (by intro tape k; rfl)
                  (fun c j => attempt_success_interval r o₁ o₂ s q weights c j) ks middle
                exact (hreplay tape final hproj.symm).1
              refine ⟨step.2, hp.2.symm.le.trans (hmono.trans hfinal), ?_, ?_⟩
              · exact congrArg some (Prod.ext ha rfl)
              · exact ⟨middle, final, by simpa only [ha] using hr, hfinal, htail⟩
      have hbound := stopped_next_bound head t f
        (ChainStepIntervalReplay.chainStep_success_interval r o₁ o₂ s.drawTrials
          q weights current.state head.length) a E
        (continuationWeight P a rest) (continuationWeight_nonneg P a rest) (by
          intro stop hstart hstop pref hf
          have hpref : (head ++ pref.val).length = stop := by
            simp only [List.length_append, pref.2]
            omega
          have hbudget : (head ++ pref.val).length + (t - (stop-head.length)) =
              head.length+t := by rw [hpref]; omega
          have ha : (classifyState a).val ≠ .invalid :=
            ChainStepNoninvalid.chainStep_noninvalid r o₁ o₂ _ s.drawTrials q weights
              current.state head.length (a,stop) hvalid hf
          cases hr : (recordObservation r o₁ o₂ s.ρ
              ⟨a,stop,current.counts,current.numeratorSum⟩).val with
          | none =>
            have hz : fairMass (head ++ pref.val) (t - (stop-head.length))
                (fun tape => E tape stop) = 0 := by
              unfold fairMass
              simp [E, hr]
            rw [hz]
            exact continuationWeight_nonneg P a rest
          | some middle =>
            have hp := record_preserves r o₁ o₂ s.ρ _ middle hr
            have hi := ih hks rest hrest (head ++ pref.val) (t - (stop-head.length))
              middle (hp.2.trans hpref.symm) (by simpa only [hp.1] using ha)
            have heq : fairMass (head ++ pref.val) (t - (stop-head.length))
                (fun tape => E tape stop) =
              fairMass (head ++ pref.val) (t - (stop-head.length))
                (fun tape => ∃ final : ObservationCursor n,
                  final.bitCursor ≤ (head ++ pref.val).length + (t-(stop-head.length)) ∧
                  recordedObservationTrace r o₁ o₂ tape s q weights ks (some middle) =
                    some (final,rest)) := by
              unfold fairMass
              apply Finset.sum_congr rfl
              intro bits _
              rw [hbudget]
              simp [E, hr]
            rw [heq]
            simpa only [hp.1] using hi)
      calc
        _ ≤ fairMass head t (fun tape => ∃ stop, stop ≤ head.length+t ∧
            f tape = some (a,stop) ∧ E tape stop) := fairMass_mono head t _ _ hevent
        _ ≤ fairMass head t (fun tape => ∃ stop, stop ≤ head.length+t ∧
            f tape = some (a,stop)) * continuationWeight P a rest := hbound
        _ ≤ P current.state a * continuationWeight P a rest :=
          mul_le_mul_of_nonneg_right (hstep head t current.state a
            (classified_card _ hvalid) hvalid) (continuationWeight_nonneg P a rest)
        _ = _ := rfl
