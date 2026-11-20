-- Prove2me | solution 1 for DeletionCode.ComponentFibers.singleton_fiber_count_bound
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-19T06:16:49.988582+00:00
-- url     : https://prove2.me/submissions/8899611c-cfe9-4e5d-a882-7d130b748b45

import Mathlib.Data.Fintype.Card
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Mathlib.SetTheory.Cardinal.Finite
import Lean.Elab.Tactic.Omega
import Definitions.Def_DeletionCode_ComponentFibers
import Theorems.Thm_DeletionCode_ComponentFibers_mem_fiber
import Theorems.Thm_DeletionCode_ComponentFibers_fiber_card_eq_one_iff
import Theorems.Thm_DeletionCode_ComponentFibers_sum_fiber_card
attribute [local simp] DeletionCode.ComponentFibers.mem_fiber

set_option autoImplicit true
open DeletionCode DeletionCode.ComponentFibers
open scoped BigOperators
namespace DeletionCode.ComponentFibers
theorem _root_.solution {A C : Type*} [Fintype A] [Fintype C]
    (f : A → C) (hsurj : Function.Surjective f) :
    2 * Fintype.card C ≤ Fintype.card A + Fintype.card {c : C // SingletonFiber f c} := by
  classical
  have hlocal (c : C) :
      2 ≤ (fiber f c).card + if SingletonFiber f c then 1 else 0 := by
    obtain ⟨a, ha⟩ := hsurj c
    have hpos : 0 < (fiber f c).card :=
      Finset.card_pos.mpr ⟨a, (mem_fiber f c a).mpr ha⟩
    by_cases hc : SingletonFiber f c
    · rw [if_pos hc]
      omega
    · have hne : (fiber f c).card ≠ 1 := fun h => hc ((fiber_card_eq_one_iff f c).mp h)
      rw [if_neg hc]
      omega
  have hsingle : (∑ c : C, if SingletonFiber f c then 1 else 0) =
      Fintype.card {c : C // SingletonFiber f c} := by
    rw [Fintype.card_subtype, Finset.card_eq_sum_ones, Finset.sum_filter]
  calc
    2 * Fintype.card C = ∑ _ : C, (2 : ℕ) := by simp [Nat.mul_comm]
    _ ≤ ∑ c : C, ((fiber f c).card + if SingletonFiber f c then 1 else 0) :=
      Finset.sum_le_sum (fun c _ => hlocal c)
    _ = (∑ c : C, (fiber f c).card) + (∑ c : C, if SingletonFiber f c then 1 else 0) :=
      Finset.sum_add_distrib
    _ = Fintype.card A + Fintype.card {c : C // SingletonFiber f c} := by
      rw [sum_fiber_card, hsingle]
end DeletionCode.ComponentFibers
