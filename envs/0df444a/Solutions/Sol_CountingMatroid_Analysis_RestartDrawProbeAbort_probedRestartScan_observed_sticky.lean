-- Prove2me | solution 1 for CountingMatroid.Analysis.RestartDrawProbeAbort.probedRestartScan_observed_sticky
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-10-24T15:22:17.280872+00:00
-- url     : https://prove2.me/submissions/2195de19-edf5-4780-8b06-379ed09c6c06

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
import Definitions.Def_CountingMatroid_Analysis_BoundedUniformAbortMass
import Definitions.Def_CountingMatroid_Analysis_BoundedUniformReplay
import Definitions.Def_CountingMatroid_Analysis_ChainDrawSiteReplay
import Definitions.Def_CountingMatroid_Analysis_ChainStepIntervalReplay
import Definitions.Def_CountingMatroid_Analysis_ConditionalDefectCoefficients
import Definitions.Def_CountingMatroid_Analysis_ConditionalDefectExtractionCoefficients
import Definitions.Def_CountingMatroid_Analysis_ConditionalDefectQuadratics
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
import Definitions.Def_CountingMatroid_Analysis_RelativeObservationBounds
import Definitions.Def_CountingMatroid_Analysis_RestartAttemptAccounting
import Definitions.Def_CountingMatroid_Analysis_RestartDrawProbe
import Definitions.Def_CountingMatroid_Analysis_RestartDrawProbeAbort
import Definitions.Def_CountingMatroid_Analysis_RestartReturnAbortAttribution
import Definitions.Def_CountingMatroid_Analysis_RestartStageAbortAttribution
import Definitions.Def_CountingMatroid_Analysis_ScheduleConfidence
import Definitions.Def_CountingMatroid_Analysis_ScheduleOpeningCost
import Definitions.Def_CountingMatroid_Analysis_ScheduleThermalSetupCost
import Definitions.Def_CountingMatroid_Analysis_SlotBlockSignature
import Definitions.Def_CountingMatroid_Analysis_SlotDemandPairing
import Definitions.Def_CountingMatroid_Analysis_SlotDemandRecursion
import Definitions.Def_CountingMatroid_Analysis_SlotTransportFlow
import Definitions.Def_CountingMatroid_Analysis_SquarefreeCoordinateHessian
import Definitions.Def_CountingMatroid_Analysis_StationaryMeanIdentities
import Definitions.Def_CountingMatroid_Analysis_ThreePairSignatureSchur
import Definitions.Def_CountingMatroid_Analysis_TransversalClassPartition
import Definitions.Def_CountingMatroid_Analysis_TransversalEventMean
import Definitions.Def_CountingMatroid_Analysis_TransversalPartition
import Definitions.Def_CountingMatroid_Analysis_TransversalProjection
import Definitions.Def_CountingMatroid_Interface_Pseudocode
import Definitions.Def_CountingMatroid_Interface_Pseudocode_Extension1
import Definitions.Def_CountingMatroid_Model_Operations
import Definitions.Def_CountingMatroid_Model_Prelude
import Definitions.Def_CountingMatroid_Model_Program
import Definitions.Def_CountingMatroid_Model_Run
import Definitions.Def_CountingMatroid_Model_Subroutines
import Lean
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
import Mathlib.Data.Finset.Card
import Mathlib.Data.Finset.Powerset
import Mathlib.Data.Finset.Prod
import Mathlib.Data.Finsupp.Indicator
import Mathlib.Data.Finsupp.Multiset
import Mathlib.Data.Fintype.Basic
import Mathlib.Data.Fintype.BigOperators
import Mathlib.Data.Fintype.Powerset
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

namespace CountingMatroid.Analysis.InitialRestartLaw
end CountingMatroid.Analysis.InitialRestartLaw
namespace CountingMatroid.Interface
end CountingMatroid.Interface
namespace CountingMatroid.Meta
end CountingMatroid.Meta
namespace Arlib
end Arlib
namespace CountingMatroid.Analysis.TransversalRankBridge
end CountingMatroid.Analysis.TransversalRankBridge
namespace CountingMatroid.Analysis.GreedyRankCorrect
end CountingMatroid.Analysis.GreedyRankCorrect
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
namespace CountingMatroid.Analysis.ExchangeProposalGeometry
end CountingMatroid.Analysis.ExchangeProposalGeometry
namespace CountingMatroid.Analysis.SlotLeafGeometry
end CountingMatroid.Analysis.SlotLeafGeometry
namespace CountingMatroid.Analysis.LeafExchangeProposal
end CountingMatroid.Analysis.LeafExchangeProposal
namespace CountingMatroid.Analysis.BalancedCliqueEnergy
end CountingMatroid.Analysis.BalancedCliqueEnergy
namespace CountingMatroid.Analysis.OnePairObservablePoincare
end CountingMatroid.Analysis.OnePairObservablePoincare
namespace CountingMatroid.Analysis.FiniteObservationMarkov
end CountingMatroid.Analysis.FiniteObservationMarkov
namespace CountingMatroid.Analysis.FiniteTapePrefixBound
end CountingMatroid.Analysis.FiniteTapePrefixBound
namespace CountingMatroid.Analysis.SuccessfulPrefixAbortBound
end CountingMatroid.Analysis.SuccessfulPrefixAbortBound
namespace CountingMatroid.Analysis.ChainStepNoninvalid
end CountingMatroid.Analysis.ChainStepNoninvalid
namespace CountingMatroid.Analysis.ObservationRoundDrawSites
end CountingMatroid.Analysis.ObservationRoundDrawSites
namespace CountingMatroid.Analysis.ClassifiedStateSelection
end CountingMatroid.Analysis.ClassifiedStateSelection
section


set_option autoImplicit false

/-!
A concrete ordinal pre-draw probe for the counted restart. The probe observes
an allowed chain attempt before its trials and retains its first descriptor,
including when the ensuing attempt aborts. Forgetting the descriptor preserves
both components of the counted restart, not just its public result.
No stopping law, finite-block bound, or abort attribution is asserted here.
-/
namespace CountingMatroid.Analysis.RestartDrawProbe
open CountingMatroid.Model CountingMatroid.Program CountingMatroid.Model.Operations
open CountingMatroid.Analysis.RestartAttemptAccounting
open CountingMatroid.Analysis.ObservationRoundDrawSites































/-- INTERNAL: Early stopping retains the old invariant; continuing requires
it only for actual body results. -/
private theorem while_invariant {α β : Type} (P : β → Prop)
    (f : β → α → Arlib.Computation.Charged Op Cell (Option β))
    (h : ∀ b a next, P b → (f b a).val = some next → P next)
    (xs : List α) (b : β) (hb : P b) :
    P (Arlib.Computation.Charged.foldlWhile f xs b).val := by
  induction xs generalizing b with
  | nil => exact hb
  | cons a xs ih =>
    cases hf : (f b a).val with
    | none =>
      simp only [Arlib.Computation.Charged.val] at hf ⊢
      simpa only [Arlib.Computation.Charged.foldlWhile, hf] using hb
    | some next =>
      have hn := ih next (h b a next hb hf)
      simp only [Arlib.Computation.Charged.val] at hf hn ⊢
      simpa only [Arlib.Computation.Charged.foldlWhile, hf] using hn

/-- INTERNAL: A return scan cannot overwrite a descriptor captured before
that scan, irrespective of later tape bits or of a subsequent abort.
TEXLINE: main.tex:1392-1421 -/
theorem probed_return_retains {n : ℕ} (r : ℕ) (o₁ o₂ : IndependenceOracle n)
    (tape : ℕ → Bool) (s : AnnealingSchedule) (q : ℚ) (w : Multipliers n)
    (ordinal : ℕ) (draw : Fin 3) (start : RestartCursor n) (count : ℕ)
    (d : ℕ × ℕ) :
    (probedReturn r o₁ o₂ tape s q w ordinal draw start count (some d)).val.2 = some d := by
  simp only [probedReturn, Arlib.Computation.Charged.val_bind,
    Arlib.Computation.Charged.val_pure, Arlib.Computation.Charged.repeatWhile]
  apply while_invariant (fun acc => acc.2 = some d) _ ?_
    (List.range s.restartCap) (((some start, false), count), some d) rfl
  intro acc _ next ha he
  simp only [probedBody, Arlib.Computation.Charged.val_bind,
    Arlib.Computation.Charged.val_pure, Option.map_eq_some_iff] at he
  obtain ⟨result, _, he⟩ := he
  cases he
  simp only [ha, Option.some_or]





end CountingMatroid.Analysis.RestartDrawProbe

/-! ### Run record
Newest first. History, not instruction — what this file claims is above.

* 2026-10-09 · proved · return scans retain already-captured descriptors independently of later tape; used this latch in denominator positivity.
* 2026-10-09 · proved · concrete sticky ordinal probes preserve the counted body,
  return, transition, stage, and complete restart, including the abort cost.
-/

end

section


set_option autoImplicit false

/-!
Stage-level abort attribution for one stored-parameter stage. A stage either
reaches a non-invalid continuing state, exhausts the shared restart cap, or
aborts at a draw whose descriptor is captured by a concrete sticky probe at
the matching ordinal. A probe at or beyond the stage's final count is never
disturbed by this stage's own processing. This repeats the return-level
pattern one fold level up: `countedTransition`/`probedTransition` thread no
extra `Bool`, so the induction needs no guard case analysis of its own and
instead dispatches to `return_attribution` at each element.
-/
namespace CountingMatroid.Analysis.RestartStageAbortAttribution

open CountingMatroid.Model CountingMatroid.Program CountingMatroid.Model.Operations
open CountingMatroid.Analysis.RestartAttemptAccounting
open CountingMatroid.Analysis.RestartDrawProbe
open CountingMatroid.Analysis.RestartReturnAbortAttribution

variable {n : ℕ} (r : ℕ) (o₁ o₂ : IndependenceOracle n)
  (tape : ℕ → Bool) (s : AnnealingSchedule) (q : ℚ) (w : Multipliers n)







theorem probedStageScan_nil (ordinal : ℕ) (draw : Fin 3)
    (acc : (Option (RestartCursor n) × ℕ) × Option (ℕ × ℕ)) :
    probedStageScan r o₁ o₂ tape s q w ordinal draw [] acc = acc := rfl



theorem probedStageScan_cons (ordinal : ℕ) (draw : Fin 3) (a : ℕ) (xs : List ℕ)
    (acc : (Option (RestartCursor n) × ℕ) × Option (ℕ × ℕ)) :
    probedStageScan r o₁ o₂ tape s q w ordinal draw (a :: xs) acc =
      probedStageScan r o₁ o₂ tape s q w ordinal draw xs
        (probedTransition r o₁ o₂ tape s q w ordinal draw acc).val := by
  unfold probedStageScan
  rw [Arlib.Computation.Charged.val_foldl_cons]













/-- INTERNAL: An already captured observation survives one further
`probedTransition`, whatever its underlying raw state. -/
private theorem probedTransition_observed_sticky (ordinal : ℕ) (draw : Fin 3)
    (acc : Option (RestartCursor n) × ℕ) (d : ℕ × ℕ) :
    (probedTransition r o₁ o₂ tape s q w ordinal draw (acc, some d)).val.2 = some d := by
  cases hc : acc.1 with
  | none => simp only [probedTransition, hc]; rfl
  | some current =>
    simp only [probedTransition, hc]
    exact RestartDrawProbe.probed_return_retains r o₁ o₂ tape s q w ordinal draw current
      acc.2 d

/-- INTERNAL: An already captured observation survives the whole remaining
stage, whatever its underlying raw state. -/
theorem probedStageScan_observed_sticky (ordinal : ℕ) (draw : Fin 3) (xs : List ℕ)
    (acc : Option (RestartCursor n) × ℕ) (d : ℕ × ℕ) :
    (probedStageScan r o₁ o₂ tape s q w ordinal draw xs (acc, some d)).2 = some d := by
  induction xs generalizing acc with
  | nil => rw [probedStageScan_nil]
  | cons a xs ih =>
    rw [probedStageScan_cons,
      show (probedTransition r o₁ o₂ tape s q w ordinal draw (acc, some d)).val =
        ((probedTransition r o₁ o₂ tape s q w ordinal draw (acc, some d)).val.1, some d) from
        Prod.ext rfl (probedTransition_observed_sticky r o₁ o₂ tape s q w ordinal draw acc d)]
    exact ih _





/-- INTERNAL: `probedStage`'s public value in terms of `probedStageScan`, at
the stored stage parameters it actually computes from `index` and
`tables`. -/
theorem probedStage_eq (tables : LearnedWeights n) (ordinal : ℕ) (draw : Fin 3)
    (index : ℕ) (acc : (Option (RestartCursor n) × ℕ) × Option (ℕ × ℕ)) :
    (probedStage r o₁ o₂ tape s tables ordinal draw index acc).val =
      probedStageScan r o₁ o₂ tape s (ratPower s.ρ (index + 1)).val
        (learnedWeightRead tables (index + 1) s.L).val ordinal draw (List.range s.τ) acc := by
  unfold probedStage probedStageScan
  simp only [Arlib.Computation.Charged.val_bind, Model.Operations.successor,
    Arlib.Computation.Charged.val_op, Arlib.Computation.Charged.repeatFor]



end CountingMatroid.Analysis.RestartStageAbortAttribution

end

section


set_option autoImplicit false

/-!
Deterministic failure attribution for concrete ordinal probes. Neither tape
coverage nor stopping-prefix replay enters this operational loop invariant.
The restart-level fold repeats the stage-level pattern from
`RestartStageAbortAttribution` one level up, using `stage_attribution` as
the per-index leaf fact: each stored-parameter stage either continues,
exhausts the shared restart cap, or aborts at a concretely captured draw.
-/
namespace CountingMatroid.Analysis.RestartDrawProbeAbort
open CountingMatroid.Model CountingMatroid.Program
open CountingMatroid.Analysis.RestartAttemptAccounting
open CountingMatroid.Analysis.RestartDrawProbe
open CountingMatroid.Analysis.RestartStageAbortAttribution

variable {n : ℕ} (r : ℕ) (o₁ o₂ : IndependenceOracle n)
  (tape : ℕ → Bool) (s : AnnealingSchedule) (tables : LearnedWeights n)







theorem probedRestartScan_nil (ordinal : ℕ) (draw : Fin 3)
    (acc : (Option (RestartCursor n) × ℕ) × Option (ℕ × ℕ)) :
    probedRestartScan r o₁ o₂ tape s tables ordinal draw [] acc = acc := rfl



theorem probedRestartScan_cons (ordinal : ℕ) (draw : Fin 3) (a : ℕ) (xs : List ℕ)
    (acc : (Option (RestartCursor n) × ℕ) × Option (ℕ × ℕ)) :
    probedRestartScan r o₁ o₂ tape s tables ordinal draw (a :: xs) acc =
      probedRestartScan r o₁ o₂ tape s tables ordinal draw xs
        (probedStage r o₁ o₂ tape s tables ordinal draw a acc).val := by
  unfold probedRestartScan
  rw [Arlib.Computation.Charged.val_foldl_cons]













end CountingMatroid.Analysis.RestartDrawProbeAbort

/-! ### Run record
Newest first. History, not instruction — what this file claims is above.

* 2026-10-09 · proved · restart-level fold (`restartScan_attr`) repeats the
  stage-level attribution pattern one level up using `stage_attribution` as
  the per-index leaf fact, closing `restart_draw_probe_abort`.
-/

end
set_option autoImplicit false

/-!
Deterministic failure attribution for concrete ordinal probes. Neither tape
coverage nor stopping-prefix replay enters this operational loop invariant.
The restart-level fold repeats the stage-level pattern from
`RestartStageAbortAttribution` one level up, using `stage_attribution` as
the per-index leaf fact: each stored-parameter stage either continues,
exhausts the shared restart cap, or aborts at a concretely captured draw.
-/
namespace CountingMatroid.Analysis.RestartDrawProbeAbort
end CountingMatroid.Analysis.RestartDrawProbeAbort
open CountingMatroid CountingMatroid.Analysis CountingMatroid.Analysis.RestartDrawProbeAbort
open CountingMatroid.Model CountingMatroid.Program
open CountingMatroid.Analysis.RestartAttemptAccounting
open CountingMatroid.Analysis.RestartDrawProbe
open CountingMatroid.Analysis.RestartStageAbortAttribution

variable {n : ℕ} (r : ℕ) (o₁ o₂ : IndependenceOracle n)
  (tape : ℕ → Bool) (s : AnnealingSchedule) (tables : LearnedWeights n)

/-- INTERNAL: An already captured observation survives the whole remaining
restart, whatever its underlying raw state. -/
theorem solution (ordinal : ℕ) (draw : Fin 3) (xs : List ℕ)
    (acc : Option (RestartCursor n) × ℕ) (d : ℕ × ℕ) :
    (probedRestartScan r o₁ o₂ tape s tables ordinal draw xs (acc, some d)).2 = some d := by
  induction xs generalizing acc with
  | nil => rw [probedRestartScan_nil]
  | cons a xs ih =>
    rw [probedRestartScan_cons, probedStage_eq,
      show (probedStageScan r o₁ o₂ tape s (ratPower s.ρ (a + 1)).val
            (Model.Operations.learnedWeightRead tables (a + 1) s.L).val ordinal draw
            (List.range s.τ) (acc, some d)) =
          ((probedStageScan r o₁ o₂ tape s (ratPower s.ρ (a + 1)).val
            (Model.Operations.learnedWeightRead tables (a + 1) s.L).val ordinal draw
            (List.range s.τ) (acc, some d)).1, some d) from
        Prod.ext rfl (probedStageScan_observed_sticky r o₁ o₂ tape s
          (ratPower s.ρ (a + 1)).val
          (Model.Operations.learnedWeightRead tables (a + 1) s.L).val ordinal draw
          (List.range s.τ) acc d)]
    exact ih _
