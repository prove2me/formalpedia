-- Prove2me | solution 1 for CountingMatroid.Analysis.FinishPhaseEmpiricalUpdate.finishPhase_empirical_update
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-10-24T14:11:13.610601+00:00
-- url     : https://prove2.me/submissions/2e33c571-41eb-423d-9863-d5530a295a19

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
import Definitions.Def_CountingMatroid_Analysis_FinishPhaseEmpiricalUpdate
import Definitions.Def_CountingMatroid_Model_Operations
import Definitions.Def_CountingMatroid_Model_Prelude
import Definitions.Def_CountingMatroid_Model_Program
import Definitions.Def_CountingMatroid_Model_Subroutines
import Lean
import Mathlib.Algebra.BigOperators.Group.Finset.Defs
import Mathlib.Algebra.BigOperators.Ring.Finset
import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Mathlib.Algebra.Order.Field.Basic
import Mathlib.Algebra.Order.Floor.Defs
import Mathlib.Algebra.Order.Group.Int
import Mathlib.Combinatorics.Matroid.Rank.ENat
import Mathlib.Data.BitVec
import Mathlib.Data.Finset.Card
import Mathlib.Data.Finset.Powerset
import Mathlib.Data.Finset.Prod
import Mathlib.Data.Fintype.Basic
import Mathlib.Data.List.Basic
import Mathlib.Data.List.Nodup
import Mathlib.Data.List.Sort
import Mathlib.Data.Multiset.Basic
import Mathlib.Data.Nat.Log
import Mathlib.Data.Rat.Defs
import Mathlib.Data.Real.Basic
import Mathlib.Order.Interval.Set.Basic
import Mathlib.Tactic.Abel
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.GCongr
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Push
import Mathlib.Tactic.Ring
import Mathlib.Tactic.Ring.RingNF

namespace CountingMatroid.Meta
end CountingMatroid.Meta
namespace Arlib
end Arlib
section


set_option autoImplicit false

namespace CountingMatroid.Analysis.FinishPhaseEmpiricalUpdate

open CountingMatroid.Model CountingMatroid.Model.Operations CountingMatroid.Program

/-- INTERNAL: Exactly-once coordinate updates in a duplicate-free scan. -/
private theorem fold_coordinate_once {α β : Type} [DecidableEq α]
    (key : β → α) (factor : β → ℚ) (l : List α) (hnodup : l.Nodup)
    (weights : β → ℚ) (index : β) :
    (l.foldl (fun w a b => if key b = a then w b * factor b else w b) weights) index =
      if key index ∈ l then weights index * factor index else weights index := by
  induction l generalizing weights with
  | nil => simp
  | cons a l ih =>
      rw [List.nodup_cons] at hnodup
      rw [List.foldl_cons, ih hnodup.2]
      by_cases he : key index = a
      · simp [he, hnodup.1]
      · simp [he]

/-- INTERNAL: A scan of successful optional computations is its pure value
fold; this keeps the actual Charged scan rather than asserting a new program. -/
private theorem fold_some_value {α β : Type}
    (f : Option β → α → Arlib.Computation.Charged Op Cell (Option β))
    (g : β → α → β) (hf : ∀ b a, (f (some b) a).val = some (g b a))
    (l : List α) (initial : β) :
    (Arlib.Computation.Charged.foldl f l (some initial)).val =
      some (l.foldl g initial) := by
  induction l generalizing initial with
  | nil => rfl
  | cons a l ih =>
      rw [Arlib.Computation.Charged.val_foldl_cons, hf, ih, List.foldl_cons]





end CountingMatroid.Analysis.FinishPhaseEmpiricalUpdate

/-! ### Run record
Newest first. History, not instruction — what this file claims is above.

* recovery · proved · evaluated the optional nested scan via a duplicate-free
  product of index lists; each off-diagonal multiplier is updated exactly once.
  Positive counts remove aborts and common observation normalization cancels.
* recovery · rejected handoff · scheduler mechanically rejected the finishing
  lemma without a further diagnostic; retained ownership and proved it locally.
-/

end
set_option autoImplicit false

namespace CountingMatroid.Analysis.FinishPhaseEmpiricalUpdate
end CountingMatroid.Analysis.FinishPhaseEmpiricalUpdate
open CountingMatroid CountingMatroid.Analysis CountingMatroid.Analysis.FinishPhaseEmpiricalUpdate

open CountingMatroid.Model CountingMatroid.Model.Operations CountingMatroid.Program

/-- INTERNAL: Positive empirical type counts make the actual nested finishing
scan succeed, with precisely the ratio and multiplier updates of the paper.
This is a deterministic statement, including an empty defect-index family.
TEXLINE: main.tex:1181-1201 -/
theorem solution {n : ℕ} (s : AnnealingSchedule) (j : ℕ)
    (weights : Multipliers n) (observed : ObservationCursor n)
    (hN : 0 < s.observations) (hzero : 0 < observed.counts .transversal)
    (hdefect : ∀ index : DefectIndex n,
      0 < observed.counts (.defect index.emptyPair index.fullPair)) :
    (finishPhase s j weights observed).val =
      some (observed.numeratorSum / (observed.counts .transversal : ℚ),
        empiricalWeights s j weights observed) := by
  classical
  let factor : DefectIndex n → ℚ := fun index => if j + 1 < s.L then
    ((observed.counts .transversal : ℚ) / (s.observations : ℚ)) /
      ((observed.counts (.defect index.emptyPair index.fullPair) : ℚ) /
        (s.observations : ℚ)) else 1
  let key : DefectIndex n → Fin n × Fin n :=
    fun index => (index.emptyPair, index.fullPair)
  let action : Multipliers n → Fin n × Fin n → Multipliers n :=
    fun w pair index => if key index = pair then w index * factor index else w index
  let step : Fin n → Option (Multipliers n) → Fin n →
      Arlib.Computation.Charged Op Cell (Option (Multipliers n)) :=
    fun i current k => do
      match current with
      | none => pure none
      | some current =>
          let diagonal ← indexEqual i k
          if diagonal then pure (some current)
          else
            if h : i ≠ k then
              let count ← countRead observed.counts (.defect i k)
              let zero ← natEqual count 0
              if zero then pure none
              else if (lessThan (successor j).val s.L).val then
                let pCount ← ratOfNat count
                let pDefect ← ratDiv pCount (s.observations : ℚ)
                let old ← multiplierRead current ⟨i, k, h⟩
                let numerator ← ratMul old
                  ((observed.counts .transversal : ℚ) / (s.observations : ℚ))
                let value ← ratDiv numerator pDefect
                let newer ← multiplierWrite current ⟨i, k, h⟩ value
                pure (some newer)
              else pure (some current)
            else pure none
  have hstep : ∀ i w k, (step i (some w) k).val = some (action w (i, k)) := by
    intro i w k
    by_cases hik : i = k
    · subst k
      have hid : action w (i, i) = w := by
        funext index
        have hnot : key index ≠ (i, i) := by
          intro he
          have he₁ := congrArg Prod.fst he
          have he₂ := congrArg Prod.snd he
          exact index.distinct (he₁.trans he₂.symm)
        simp [action, hnot]
      simp [step, indexEqual, hid]
    · have hcount : observed.counts (.defect i k) ≠ 0 :=
        Nat.ne_of_gt (hdefect ⟨i, k, hik⟩)
      simp only [step, Arlib.Computation.Charged.val_bind]
      simp only [indexEqual, Arlib.Computation.Charged.val_op, beq_iff_eq,
        hik, if_false, dif_pos hik]
      simp only [Arlib.Computation.Charged.val_bind, countRead,
        Arlib.Computation.Charged.val_opMany, natEqual,
        Arlib.Computation.Charged.val_op, beq_iff_eq, hcount, if_false,
        successor, lessThan]
      by_cases hj : j + 1 < s.L
      · simp only [hj, decide_true, if_true, Arlib.Computation.Charged.val_bind,
          ratOfNat, ratDiv, ratMul, multiplierRead, multiplierWrite,
          Arlib.Computation.Charged.val_opMany, Arlib.Computation.Charged.val_pure,
          Option.some.injEq]
        funext index
        have he : index = (⟨i, k, hik⟩ : DefectIndex n) ↔ key index = (i, k) := by
          constructor
          · rintro rfl
            rfl
          · intro he
            cases index with
            | mk empty full distinct =>
                obtain ⟨rfl, rfl⟩ := Prod.mk.inj he
                rfl
        simp only [action, factor, hj, if_true]
        by_cases heq : key index = (i, k)
        · have heidx := he.mpr heq
          subst index
          simp [key, mul_div_assoc]
        · simp [heq, not_congr he |>.mpr heq]
      · simp [hj, action, factor]

  have hinner : ∀ w i,
      (Arlib.Computation.Charged.foldl (step i) (List.finRange n) (some w)).val =
        some ((List.finRange n).foldl (fun w k => action w (i, k)) w) := by
    intro w i
    exact fold_some_value (step i) (fun w k => action w (i, k)) (hstep i)
      (List.finRange n) w
  have hscan : (Arlib.Computation.Charged.foldl
      (fun acc i => Arlib.Computation.Charged.foldl (step i) (List.finRange n) acc)
      (List.finRange n) (some weights)).val =
      some (empiricalWeights s j weights observed) := by
    rw [fold_some_value _ _ hinner]
    congr 1
    have hpure : (List.finRange n).foldl
        (fun w i => (List.finRange n).foldl (fun w k => action w (i, k)) w) weights =
        ((List.finRange n).product (List.finRange n)).foldl action weights := by
      simp only [List.product, List.foldl_flatMap, List.foldl_map]
    rw [hpure]
    funext index
    have hcoord : (((List.finRange n).product (List.finRange n)).foldl action weights) index =
        weights index * factor index := by
      have hc := fold_coordinate_once key factor _
        ((List.nodup_finRange n).product (List.nodup_finRange n)) weights index
      have hm : key index ∈ List.finRange n ×ˢ List.finRange n := by simp [key]
      rw [if_pos hm] at hc
      simpa only [action, SProd.sprod] using hc
    rw [hcoord]
    dsimp [factor, empiricalWeights]
    by_cases hj : j + 1 < s.L
    · rw [if_pos hj, if_pos hj]
      have hNq : (s.observations : ℚ) ≠ 0 := by exact_mod_cast Nat.ne_of_gt hN
      field_simp
    · simp [hj]
  simp only [finishPhase, Arlib.Computation.Charged.val_bind]
  have hnonzero : (natEqual (countRead observed.counts .transversal).val 0).val = false := by
    simp [natEqual, countRead, Nat.ne_of_gt hzero]
  rw [hnonzero]
  simp only [Bool.false_eq_true, if_false, Arlib.Computation.Charged.val_bind,
    ratOfNat, ratDiv, countRead, Arlib.Computation.Charged.val_opMany]
  change (match (Arlib.Computation.Charged.foldl
      (fun acc i => Arlib.Computation.Charged.foldl (step i) (List.finRange n) acc)
      (List.finRange n) (some weights)).val with
    | none => pure none
    | some updated => pure (some
        ((observed.numeratorSum / (s.observations : ℚ)) /
          ((observed.counts .transversal : ℚ) / (s.observations : ℚ)), updated)) :
    Arlib.Computation.Charged Op Cell (Option (ℚ × Multipliers n))).val = _
  rw [hscan]
  simp only [Arlib.Computation.Charged.val_pure, Option.some.injEq, Prod.mk.injEq,
    and_true]
  have hNq : (s.observations : ℚ) ≠ 0 := by exact_mod_cast Nat.ne_of_gt hN
  field_simp
