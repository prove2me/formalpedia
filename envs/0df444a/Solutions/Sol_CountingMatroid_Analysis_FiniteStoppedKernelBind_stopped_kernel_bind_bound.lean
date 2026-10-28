-- Prove2me | solution 1 for CountingMatroid.Analysis.FiniteStoppedKernelBind.stopped_kernel_bind_bound
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-10-24T16:13:44.007291+00:00
-- url     : https://prove2.me/submissions/6d59050a-026b-4ae0-8e78-f6e2a80e21ae

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
import Definitions.Def_CountingMatroid_Analysis_ChainStepIntervalReplay
import Definitions.Def_CountingMatroid_Analysis_FiniteStoppedFiberMass
import Definitions.Def_CountingMatroid_Model_Operations
import Definitions.Def_CountingMatroid_Model_Prelude
import Definitions.Def_CountingMatroid_Model_Program
import Definitions.Def_CountingMatroid_Model_Subroutines
import Lean
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
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
import Mathlib.Data.Fintype.Vector
import Mathlib.Data.List.Basic
import Mathlib.Data.List.Nodup
import Mathlib.Data.List.Sort
import Mathlib.Data.Multiset.Basic
import Mathlib.Data.Nat.Log
import Mathlib.Data.Rat.Defs
import Mathlib.Data.Real.Basic
import Mathlib.Order.Interval.Set.Basic
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
import Theorems.Thm_CountingMatroid_Analysis_FiniteStoppedFiberMass_stopped_fiber_bound

namespace CountingMatroid.Meta
end CountingMatroid.Meta
namespace Arlib
end Arlib
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
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

/-! A finite stopped operation can be followed by a uniformly bounded fresh
continuation without conditioning away its abort mass. -/
namespace CountingMatroid.Analysis.FiniteStoppedKernelBind
end CountingMatroid.Analysis.FiniteStoppedKernelBind
open CountingMatroid CountingMatroid.Analysis CountingMatroid.Analysis.FiniteStoppedKernelBind
open CountingMatroid.Analysis.FiniteStoppedFiberMass

/-- INTERNAL: Disintegrate an adaptive initializer by its complete successful
result and consumed prefix, then apply a fresh-suffix continuation bound.
Only initializer results occurring in the continued event need be covered.
TEXLINE: main.tex:1163-1176,1392-1421 -/
theorem solution {α : Type} (head : List Bool) (t : ℕ)
    (f : (ℕ → Bool) → Option α) (cursor : α → ℕ)
    (hf : ChainStepIntervalReplay.SuccessReplay f cursor head.length)
    (E : (ℕ → Bool) → α → Prop) (B : α → ℝ) (hB : ∀ a, 0 ≤ B a)
    (hcovered : ∀ bits : List.Vector Bool t, ∀ a,
      f (finiteTape (head ++ bits.val)) = some a →
      E (finiteTape (head ++ bits.val)) a → cursor a ≤ head.length + t)
    (hcont : ∀ a, head.length ≤ cursor a → cursor a ≤ head.length + t →
      ∀ pref : List.Vector Bool (cursor a - head.length),
      f (finiteTape (head ++ pref.val)) = some a →
      fairMass (head ++ pref.val) (t - (cursor a - head.length))
        (fun tape => E tape a) ≤ B a) :
    fairMass head t (fun tape => ∃ a, f tape = some a ∧ E tape a) ≤
      ∑ bits : List.Vector Bool t, (1 / (2 : ℝ) ^ t) *
        ((f (finiteTape (head ++ bits.val))).map B).getD 0 := by
  classical
  let R := fun bits : List.Vector Bool t => f (finiteTape (head ++ bits.val))
  let S := Finset.univ.image R
  let C := fun tape outcome => match outcome with
    | none => False
    | some a => E tape a
  have hleft : fairMass head t (fun tape => ∃ a, f tape = some a ∧ E tape a) =
      ∑ outcome ∈ S, fairMass head t (fun tape => f tape = outcome ∧ C tape outcome) := by
    unfold fairMass
    rw [Finset.sum_comm]
    apply Finset.sum_congr rfl
    intro bits _
    have hm : R bits ∈ S := Finset.mem_image_of_mem _ (Finset.mem_univ bits)
    have he : (∃ a, f (finiteTape (head ++ bits.val)) = some a ∧
        E (finiteTape (head ++ bits.val)) a) ↔ C (finiteTape (head ++ bits.val)) (R bits) := by
      cases hr : R bits with
      | none => simp +instances [R] at hr; simp [hr, C]
      | some a => simp +instances [R] at hr; simp [hr, C]
    dsimp only
    simp +instances only [he]
    rw [Finset.sum_eq_single (R bits)]
    · simp +instances only [show f (finiteTape (head ++ bits.val)) = R bits from rfl,
        true_and]
    · intro other _ hne
      exact if_neg (fun h => hne h.1.symm)
    · exact fun h => False.elim (h hm)
  have hright : (∑ bits : List.Vector Bool t, (1 / (2 : ℝ) ^ t) *
      ((f (finiteTape (head ++ bits.val))).map B).getD 0) =
      ∑ outcome ∈ S, fairMass head t (fun tape => f tape = outcome) *
        (outcome.map B).getD 0 := by
    unfold fairMass
    simp only [Finset.sum_mul]
    rw [Finset.sum_comm]
    apply Finset.sum_congr rfl
    intro bits _
    have hm : R bits ∈ S := Finset.mem_image_of_mem _ (Finset.mem_univ bits)
    change (1 / (2 : ℝ) ^ t) * ((R bits).map B).getD 0 = _
    simp only [ite_mul, zero_mul]
    change _ = ∑ outcome ∈ S,
      if R bits = outcome then (1 / (2 : ℝ) ^ t) * (outcome.map B).getD 0 else 0
    simp only [Finset.sum_ite_eq, hm, if_true]
  rw [hleft, hright]
  apply Finset.sum_le_sum
  intro outcome _
  cases outcome with
  | none =>
    simp only [C, and_false, fairMass, if_false, Finset.sum_const_zero,
      Option.map_none, Option.getD_none, mul_zero, le_refl]
  | some a =>
    simp only [C, Option.map_some, Option.getD_some]
    by_cases hocc : ∃ bits : List.Vector Bool t,
      f (finiteTape (head ++ bits.val)) = some a ∧ E (finiteTape (head ++ bits.val)) a
    · obtain ⟨bits, hfa, hEa⟩ := hocc
      exact stopped_fiber_bound head t f cursor hf a (hf _ a hfa).1
        (hcovered bits a hfa hEa) (fun tape => E tape a) (B a) (hB a)
        (hcont a (hf _ a hfa).1 (hcovered bits a hfa hEa))
    · have hz : fairMass head t (fun tape => f tape = some a ∧ E tape a) = 0 := by
        unfold fairMass
        apply Finset.sum_eq_zero
        intro bits _
        exact if_neg (fun h => hocc ⟨bits, h⟩)
      rw [hz]
      exact mul_nonneg (fairMass_nonneg _ _ _) (hB a)
