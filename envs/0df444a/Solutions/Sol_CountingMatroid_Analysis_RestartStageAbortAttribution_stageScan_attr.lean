-- Prove2me | solution 1 for CountingMatroid.Analysis.RestartStageAbortAttribution.stageScan_attr
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-10-24T16:36:17.532428+00:00
-- url     : https://prove2.me/submissions/b019a745-4a80-441b-b8d0-c727d4b3cc79

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
import Definitions.Def_CountingMatroid_Analysis_AnnealingPartitionDrift
import Definitions.Def_CountingMatroid_Analysis_BoundedRunPhase
import Definitions.Def_CountingMatroid_Analysis_BoundedRunPhaseHistory
import Definitions.Def_CountingMatroid_Analysis_BoundedRunPhaseWork
import Definitions.Def_CountingMatroid_Analysis_BoundedUniformAbortMass
import Definitions.Def_CountingMatroid_Analysis_BoundedUniformReplay
import Definitions.Def_CountingMatroid_Analysis_ChainDrawSiteReplay
import Definitions.Def_CountingMatroid_Analysis_ChainStepIntervalReplay
import Definitions.Def_CountingMatroid_Analysis_DefectPartitionPositive
import Definitions.Def_CountingMatroid_Analysis_EmpiricalPhaseCertificate
import Definitions.Def_CountingMatroid_Analysis_EstimateMedianResource
import Definitions.Def_CountingMatroid_Analysis_FinishPhaseEmpiricalUpdate
import Definitions.Def_CountingMatroid_Analysis_FinishPhaseWork
import Definitions.Def_CountingMatroid_Analysis_FirstPhaseFailure
import Definitions.Def_CountingMatroid_Analysis_InitialMultipliersGood
import Definitions.Def_CountingMatroid_Analysis_ObservePhaseWork
import Definitions.Def_CountingMatroid_Analysis_PhaseChainWork
import Definitions.Def_CountingMatroid_Analysis_PhaseMeanCertificate
import Definitions.Def_CountingMatroid_Analysis_PhaseObservationExperiment
import Definitions.Def_CountingMatroid_Analysis_PhaseResourcePrimitives
import Definitions.Def_CountingMatroid_Analysis_RationalHeight
import Definitions.Def_CountingMatroid_Analysis_RelativeObservationBounds
import Definitions.Def_CountingMatroid_Analysis_RestartAttemptAccounting
import Definitions.Def_CountingMatroid_Analysis_RestartDrawProbe
import Definitions.Def_CountingMatroid_Analysis_RestartReturnAbortAttribution
import Definitions.Def_CountingMatroid_Analysis_RestartStageAbortAttribution
import Definitions.Def_CountingMatroid_Analysis_ScheduleConfidence
import Definitions.Def_CountingMatroid_Analysis_ScheduleOpeningCost
import Definitions.Def_CountingMatroid_Analysis_ScheduleThermalSetupCost
import Definitions.Def_CountingMatroid_Analysis_StationaryMeanIdentities
import Definitions.Def_CountingMatroid_Analysis_TransversalClassPartition
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
import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Mathlib.Algebra.Order.Field.Basic
import Mathlib.Algebra.Order.Floor.Defs
import Mathlib.Algebra.Order.Group.Int
import Mathlib.Algebra.Order.Ring.Pow
import Mathlib.Analysis.Complex.ExponentialBounds
import Mathlib.Combinatorics.Matroid.Rank.ENat
import Mathlib.Data.BitVec
import Mathlib.Data.ENNReal.Inv
import Mathlib.Data.Finset.Card
import Mathlib.Data.Finset.Powerset
import Mathlib.Data.Finset.Prod
import Mathlib.Data.Fintype.Basic
import Mathlib.Data.Fintype.BigOperators
import Mathlib.Data.List.Basic
import Mathlib.Data.List.Induction
import Mathlib.Data.List.Infix
import Mathlib.Data.List.Nodup
import Mathlib.Data.List.OfFn
import Mathlib.Data.List.Sort
import Mathlib.Data.Multiset.Basic
import Mathlib.Data.Nat.Log
import Mathlib.Data.Rat.Defs
import Mathlib.Data.Real.Basic
import Mathlib.Data.Set.Card.Arithmetic
import Mathlib.Data.Set.Finite.List
import Mathlib.Order.Interval.Set.Basic
import Mathlib.Probability.ProbabilityMassFunction.Constructions
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
import Theorems.Thm_CountingMatroid_Analysis_RestartReturnAbortAttribution_return_attribution

namespace CountingMatroid.Meta
end CountingMatroid.Meta
namespace Arlib
end Arlib
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





theorem rawStage_nil (acc : Option (RestartCursor n) × ℕ) :
    rawStage r o₁ o₂ tape s q w [] acc = acc := rfl

theorem probedStageScan_nil (ordinal : ℕ) (draw : Fin 3)
    (acc : (Option (RestartCursor n) × ℕ) × Option (ℕ × ℕ)) :
    probedStageScan r o₁ o₂ tape s q w ordinal draw [] acc = acc := rfl

theorem rawStage_cons (a : ℕ) (xs : List ℕ) (acc : Option (RestartCursor n) × ℕ) :
    rawStage r o₁ o₂ tape s q w (a :: xs) acc =
      rawStage r o₁ o₂ tape s q w xs (countedTransition r o₁ o₂ tape s q w acc).val := by
  unfold rawStage
  rw [Arlib.Computation.Charged.val_foldl_cons]

theorem probedStageScan_cons (ordinal : ℕ) (draw : Fin 3) (a : ℕ) (xs : List ℕ)
    (acc : (Option (RestartCursor n) × ℕ) × Option (ℕ × ℕ)) :
    probedStageScan r o₁ o₂ tape s q w ordinal draw (a :: xs) acc =
      probedStageScan r o₁ o₂ tape s q w ordinal draw xs
        (probedTransition r o₁ o₂ tape s q w ordinal draw acc).val := by
  unfold probedStageScan
  rw [Arlib.Computation.Charged.val_foldl_cons]

/-- INTERNAL: A `none` state is absorbing for `countedTransition`. -/
private theorem countedTransition_none (cnt : ℕ) :
    (countedTransition r o₁ o₂ tape s q w (none, cnt)).val = (none, cnt) := rfl



/-- INTERNAL: A live state defers to `countedReturn`. -/
private theorem countedTransition_some (current : RestartCursor n) (cnt : ℕ) :
    (countedTransition r o₁ o₂ tape s q w (some current, cnt)).val =
      (countedReturn r o₁ o₂ tape s q w current cnt).val := rfl

/-- INTERNAL: A live state defers to `probedReturn`. -/
private theorem probedTransition_some (ordinal : ℕ) (draw : Fin 3) (current : RestartCursor n)
    (cnt : ℕ) (observed : Option (ℕ × ℕ)) :
    (probedTransition r o₁ o₂ tape s q w ordinal draw ((some current, cnt), observed)).val =
      (probedReturn r o₁ o₂ tape s q w ordinal draw current cnt observed).val := rfl

/-- INTERNAL: Once aborted, no further elements of the list change the raw
accumulator. -/
theorem rawStage_done (xs : List ℕ) (cnt : ℕ) :
    rawStage r o₁ o₂ tape s q w xs (none, cnt) = (none, cnt) := by
  induction xs with
  | nil => rw [rawStage_nil]
  | cons a xs ih => rw [rawStage_cons, countedTransition_none]; exact ih



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









end CountingMatroid.Analysis.RestartStageAbortAttribution

end
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
end CountingMatroid.Analysis.RestartStageAbortAttribution
open CountingMatroid CountingMatroid.Analysis CountingMatroid.Analysis.RestartStageAbortAttribution

open CountingMatroid.Model CountingMatroid.Program CountingMatroid.Model.Operations
open CountingMatroid.Analysis.RestartAttemptAccounting
open CountingMatroid.Analysis.RestartDrawProbe
open CountingMatroid.Analysis.RestartReturnAbortAttribution

variable {n : ℕ} (r : ℕ) (o₁ o₂ : IndependenceOracle n)
  (tape : ℕ → Bool) (s : AnnealingSchedule) (q : ℚ) (w : Multipliers n)

/-- INTERNAL: Positivity/attribution target for one stage scan, generalized
over an arbitrary remaining list and starting accumulator. -/
theorem solution :
    ∀ (xs : List ℕ) (current : RestartCursor n) (count : ℕ),
      (classifyState current.state).val ≠ .invalid → current.attempts = count →
      count ≤ (rawStage r o₁ o₂ tape s q w xs (some current, count)).2 ∧
      ((∃ final : RestartCursor n,
          (rawStage r o₁ o₂ tape s q w xs (some current, count)).1 = some final ∧
          (classifyState final.state).val ≠ .invalid ∧
          final.attempts = (rawStage r o₁ o₂ tape s q w xs (some current, count)).2 ∧
          ∀ ordinal (draw : Fin 3),
            (rawStage r o₁ o₂ tape s q w xs (some current, count)).2 ≤ ordinal →
            probedStageScan r o₁ o₂ tape s q w ordinal draw xs ((some current, count), none) =
              (rawStage r o₁ o₂ tape s q w xs (some current, count), none))
        ∨ ((rawStage r o₁ o₂ tape s q w xs (some current, count)).1 = none ∧
            s.restartCap ≤ (rawStage r o₁ o₂ tape s q w xs (some current, count)).2)
        ∨ ((rawStage r o₁ o₂ tape s q w xs (some current, count)).1 = none ∧
            ∃ (ordinal : ℕ) (draw : Fin 3) (d : ℕ × ℕ), count ≤ ordinal ∧
              ordinal < s.restartCap ∧
              (boundedUniform tape s.drawTrials d.2 d.1).val.1 = none ∧
              (probedStageScan r o₁ o₂ tape s q w ordinal draw xs
                ((some current, count), none)).2 = some d)) := by
  intro xs
  induction xs with
  | nil =>
    intro current count hvalid hinv
    rw [rawStage_nil]
    exact ⟨le_refl _, Or.inl ⟨current, rfl, hvalid, hinv, fun ordinal draw _ => by
      rw [probedStageScan_nil]⟩⟩
  | cons a xs ih =>
    intro current count hvalid hinv
    obtain ⟨hle, hcases⟩ := return_attribution r o₁ o₂ tape s q w current count hvalid hinv
    rcases hcases with ⟨final, hfinal1, hfinal2, hfinal3, hfinal4⟩
      | ⟨hcapped1, hcapped2⟩ | ⟨ordinal₀, draw₀, d₀, hge₀, hcapord₀, habort1, hfail, hcap⟩
    · have hpair : (countedReturn r o₁ o₂ tape s q w current count).val =
          (some final, (countedReturn r o₁ o₂ tape s q w current count).val.2) :=
        Prod.ext hfinal1 rfl
      rw [rawStage_cons, countedTransition_some, hpair]
      obtain ⟨hle2, hcases2⟩ := ih final _ hfinal2 hfinal3
      refine ⟨by omega, ?_⟩
      rcases hcases2 with ⟨final2, h1, h2, h3, h4⟩ | ⟨hc1, hc2⟩
        | ⟨hc1, ord, draw, d, hge, hcapord, hfail2, hc2⟩
      · refine Or.inl ⟨final2, h1, h2, h3, ?_⟩
        intro ordinal draw hord
        rw [probedStageScan_cons, probedTransition_some, hfinal4 ordinal draw
          (by omega), hpair]
        exact h4 ordinal draw hord
      · exact Or.inr (Or.inl ⟨hc1, hc2⟩)
      · refine Or.inr (Or.inr ⟨hc1, ord, draw, d, by omega, hcapord, hfail2, ?_⟩)
        rw [probedStageScan_cons, probedTransition_some, hfinal4 ord draw (by omega), hpair]
        exact hc2
    · have hpair : (countedReturn r o₁ o₂ tape s q w current count).val =
          (none, (countedReturn r o₁ o₂ tape s q w current count).val.2) :=
        Prod.ext hcapped2 rfl
      rw [rawStage_cons, countedTransition_some, hpair, rawStage_done]
      exact ⟨by omega, Or.inr (Or.inl ⟨rfl, hcapped1⟩)⟩
    · have hpair : (countedReturn r o₁ o₂ tape s q w current count).val =
          (none, (countedReturn r o₁ o₂ tape s q w current count).val.2) :=
        Prod.ext habort1 rfl
      rw [rawStage_cons, countedTransition_some, hpair, rawStage_done]
      refine ⟨by omega, Or.inr (Or.inr ⟨rfl, ordinal₀, draw₀, d₀, by omega, hcapord₀, hfail,
        ?_⟩)⟩
      rw [probedStageScan_cons, probedTransition_some,
        show (probedReturn r o₁ o₂ tape s q w ordinal₀ draw₀ current count none).val =
          ((probedReturn r o₁ o₂ tape s q w ordinal₀ draw₀ current count none).val.1,
            some d₀) from Prod.ext rfl hcap]
      exact probedStageScan_observed_sticky r o₁ o₂ tape s q w ordinal₀ draw₀ xs _ d₀
