-- Prove2me | solution 1 for CountingMatroid.Analysis.BoundedUniformReplay.boundedUniform_interval_replay
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-10-24T15:06:14.599925+00:00
-- url     : https://prove2.me/submissions/424c6475-8a1a-4bb4-923f-36778e51144c

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
import Definitions.Def_CountingMatroid_Analysis_BoundedUniformReplay
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

/-!
Deterministic locality of bounded rejection sampling. The cursor increases
monotonically, and agreement on the bits actually consumed determines the
whole value, including a rejected draw. No fair-bit law is assumed here.
-/

namespace CountingMatroid.Analysis.BoundedUniformReplay
open CountingMatroid.Model CountingMatroid.Model.Operations CountingMatroid.Program



/-- INTERNAL: Compose two deterministic tape operations, restricting agreement
to each successive consumed interval. -/
theorem intervalReplay_comp {α β : Type} (f : (ℕ → Bool) → α)
    (g : (ℕ → Bool) → α → β) (ca : α → ℕ) (cb : β → ℕ) (start : ℕ)
    (hf : IntervalReplay f ca start)
    (hg : ∀ a, IntervalReplay (fun tape => g tape a) cb (ca a)) :
    IntervalReplay (fun tape => g tape (f tape)) cb start := by
  intro tape
  have hfirst := hf tape
  have hsecond := hg (f tape) tape
  refine ⟨hfirst.1.trans hsecond.1, ?_⟩
  intro other hagree
  change g other (f other) = g tape (f tape)
  rw [hfirst.2 other (fun i hlo hhi => hagree i hlo (hhi.trans_le hsecond.1))]
  exact hsecond.2 other (fun i hlo hhi => hagree i (hfirst.1.trans hlo) hhi)

/-- INTERNAL: A charged fold of monotone interval-local operations is itself
monotone and interval-local. -/
theorem foldl_intervalReplay {α β : Type}
    (f : (ℕ → Bool) → β → α → Arlib.Computation.Charged Op Cell β)
    (cursor : β → ℕ)
    (hstep : ∀ b a, IntervalReplay (fun tape => (f tape b a).val) cursor (cursor b))
    (xs : List α) (b : β) :
    IntervalReplay (fun tape => (Arlib.Computation.Charged.foldl (f tape) xs b).val)
      cursor (cursor b) := by
  induction xs generalizing b with
  | nil => exact fun _ => ⟨le_rfl, fun _ _ => rfl⟩
  | cons a xs ih =>
      exact intervalReplay_comp (fun tape => (f tape b a).val)
        (fun tape b' => (Arlib.Computation.Charged.foldl (f tape) xs b').val)
        cursor cursor (cursor b) (hstep b a) ih



end CountingMatroid.Analysis.BoundedUniformReplay

/-! ### Run record
Newest first. History, not instruction — what this file claims is above.

* r21 · proved · monotone interval replay for every bounded rejection outcome,
  by nested charged-fold induction, including exhausted rejection caps.
-/

end
set_option autoImplicit false

/-!
Deterministic locality of bounded rejection sampling. The cursor increases
monotonically, and agreement on the bits actually consumed determines the
whole value, including a rejected draw. No fair-bit law is assumed here.
-/

namespace CountingMatroid.Analysis.BoundedUniformReplay
end CountingMatroid.Analysis.BoundedUniformReplay
open CountingMatroid CountingMatroid.Analysis CountingMatroid.Analysis.BoundedUniformReplay
open CountingMatroid.Model CountingMatroid.Model.Operations CountingMatroid.Program

/-- INTERNAL: Every bounded uniform draw replays on its consumed interval,
even when the rejection cap is exhausted. In particular its ending cursor
never precedes its starting cursor.
TEXLINE: main.tex:1392-1421 -/
theorem solution (trials v start : ℕ) :
    IntervalReplay (fun tape => (boundedUniform tape trials v start).val)
      Prod.snd start := by
  unfold boundedUniform
  simp only [Arlib.Computation.Charged.val_bind, lessThan, uniformWidth,
    Arlib.Computation.Charged.val_op, Arlib.Computation.Charged.val_pure, decide_eq_true_eq]
  by_cases hbad : v < 1
  · simp only [hbad, decide_true, ite_true, Arlib.Computation.Charged.val_pure]
    exact fun _ => ⟨le_rfl, fun _ _ => rfl⟩
  · simp only [hbad, decide_false, Bool.false_eq_true, ite_false,
      Arlib.Computation.Charged.val_bind, Arlib.Computation.Charged.val_op]
    by_cases hsingle : v < 2
    · simp only [hsingle, decide_true, ite_true, Arlib.Computation.Charged.val_pure]
      exact fun _ => ⟨le_rfl, fun _ _ => rfl⟩
    · simp only [hsingle, decide_false, Bool.false_eq_true, ite_false,
        Arlib.Computation.Charged.val_bind, Arlib.Computation.Charged.val_op,
        Arlib.Computation.Charged.val_pure, Arlib.Computation.Charged.repeatFor]
      apply foldl_intervalReplay
      intro acc index
      simp only [Arlib.Computation.Charged.val_bind, isSome,
        Arlib.Computation.Charged.val_op]
      by_cases hdone : acc.1.isSome = true
      · simp only [hdone, ite_true, Arlib.Computation.Charged.val_pure]
        exact fun _ => ⟨le_rfl, fun _ _ => rfl⟩
      · simp only [hdone, Bool.false_eq_true, ite_false, Arlib.Computation.Charged.val_bind,
          Arlib.Computation.Charged.val_op, Arlib.Computation.Charged.val_pure, decide_eq_true_eq]
        have htrial : IntervalReplay (fun tape =>
            (Arlib.Computation.Charged.repeatFor (fun _ (inner : ℕ × ℕ) => do
              let bit ← fairBit tape inner.2
              let value ← appendBit inner.1 bit
              let next ← successor inner.2
              pure (value, next)) ((v - 1).log2 + 1) (0, acc.2)).val)
            Prod.snd acc.2 := by
          apply foldl_intervalReplay
          intro inner i tape
          simp only [Arlib.Computation.Charged.val_bind, fairBit, appendBit, successor,
            Arlib.Computation.Charged.val_op, Arlib.Computation.Charged.val_pure, decide_eq_true_eq]
          refine ⟨Nat.le_succ _, ?_⟩
          intro other hagree
          change (2 * inner.1 + if other inner.2 then 1 else 0, inner.2 + 1) = _
          rw [hagree inner.2 le_rfl (Nat.lt_succ_self _)]
          rfl
        intro tape
        have ht := htrial tape
        dsimp only
        simp only [Arlib.Computation.Charged.val_pure, apply_ite, ite_self]
        refine ⟨ht.1, ?_⟩
        intro other hagree
        have heq := ht.2 other hagree
        dsimp only at heq ⊢
        simp only [Arlib.Computation.Charged.repeatFor] at heq
        simp only [heq]
        split <;> simp_all only [ite_true, ite_false]
