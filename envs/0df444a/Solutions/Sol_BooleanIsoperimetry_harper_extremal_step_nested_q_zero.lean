-- Prove2me | solution 1 for BooleanIsoperimetry.harper_extremal_step_nested_q_zero
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-22T07:37:39.672351+00:00
-- url     : https://prove2.me/submissions/470df5fb-c162-40cd-9f96-fcbe088d14e0

module
public import Definitions.Def_LeanPool_BooleanIsoperimetry_Cascade
public import Mathlib.Order.Interval.Finset.Nat
public import Mathlib.Algebra.BigOperators.Intervals
public import Mathlib.Algebra.Group.Action.Defs
public import Mathlib.Algebra.Order.BigOperators.Group.Finset
public import Mathlib.Data.Rat.Cast.Order
public import Mathlib.Tactic.Linarith.Frontend
public import Mathlib.Tactic.NormNum.Abs
public import Mathlib.Tactic.NormNum.DivMod
public import Mathlib.Tactic.NormNum.OfScientific
public import Definitions.Def_LeanPool_BooleanIsoperimetry_Macaulay
public import Theorems.Thm_BooleanIsoperimetry_boundaryCost_comm
public import Theorems.Thm_BooleanIsoperimetry_harper_bc_min_q_zero_core
public import Theorems.Thm_BooleanIsoperimetry_cascade_p_le
public import Theorems.Thm_BooleanIsoperimetry_H_succ_cascade
public import Theorems.Thm_BooleanIsoperimetry_H_zero
public import Theorems.Thm_BooleanIsoperimetry_cascade_split_add
public import Theorems.Thm_BooleanIsoperimetry_mem_neighborhood_iff
attribute [local simp] BooleanIsoperimetry.mem_neighborhood_iff



set_option autoImplicit true
@[expose] public section
public section
open scoped BigOperators
open BooleanIsoperimetry
namespace BooleanIsoperimetry
theorem _root_.solution (n : ℕ)
    (_ih : ∀ m, m < n + 1 → ∀ x y, x ≤ 2 ^ m → y ≤ 2 ^ m →
            H (m + 1) (x + y) ≤ max (H m x) y + max (H m y) x)
    {a b p q p0 p1 q0 q1 a0 a1 b0 b1 : ℕ}
    (ha : a ≤ 2 ^ (n + 1)) (hb : b ≤ 2 ^ (n + 1))
    (hcasc : CascadeSplit (n + 1) (a + b) p q)
    (hq_zero : q = 0)
    (_hp0 : p0 ≤ 2 ^ n) (_hp1 : p1 ≤ 2 ^ n)
    (_hq0 : q0 ≤ 2 ^ n) (_hq1 : q1 ≤ 2 ^ n)
    (_ha0 : a0 ≤ 2 ^ n) (_ha1 : a1 ≤ 2 ^ n)
    (_hb0 : b0 ≤ 2 ^ n) (_hb1 : b1 ≤ 2 ^ n)
    (hp_split : CascadeSplit n p p0 p1)
    (hq_split : CascadeSplit n q q0 q1)
    (ha_split : CascadeSplit n a a0 a1)
    (hb_split : CascadeSplit n b b0 b1) :
    max (max (H n p0) p1 + max (H n p1) p0) q +
    max (max (H n q0) q1 + max (H n q1) q0) p ≤
    max (max (H n a0) a1 + max (H n a1) a0) b +
    max (max (H n b0) b1 + max (H n b1) b0) a := by
  subst q
  have hp : p ≤ 2 ^ (n + 1) := cascade_p_le hcasc
  have hpq : p = a + b := by
    have hsum := cascade_split_add hcasc
    omega
  rw [← H_succ_cascade hp_split, ← H_succ_cascade hq_split,
      ← H_succ_cascade ha_split, ← H_succ_cascade hb_split]
  simp only [H_zero, Nat.max_zero, Nat.zero_max]
  by_cases hba : b ≤ a
  · exact harper_bc_min_q_zero_core (n + 1) ha hb hp hba hpq hcasc
  · have hab : a ≤ b := le_of_not_ge hba
    have hcasc_comm : CascadeSplit (n + 1) (b + a) p 0 := by
      simpa [Nat.add_comm] using hcasc
    have hpq_comm : p = b + a := by omega
    have h := harper_bc_min_q_zero_core (n + 1) hb ha hp hab hpq_comm hcasc_comm
    rwa [boundaryCost_comm (n + 1) a b]
end BooleanIsoperimetry
