-- Prove2me | solution 1 for BooleanIsoperimetry.harper_bc_min
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-22T08:03:44.09375+00:00
-- url     : https://prove2.me/submissions/27fa37f4-a06d-4855-949b-86cd2007c3f8

module
public import Definitions.Def_LeanPool_BooleanIsoperimetry_Macaulay
public import Definitions.Def_LeanPool_BooleanIsoperimetry_Shadow
public import Mathlib.Algebra.BigOperators.Intervals
public import Mathlib.Data.Rat.Cast.Order
public import Mathlib.Tactic.FinCases
public import Mathlib.Tactic.NormNum.Abs
public import Mathlib.Tactic.NormNum.DivMod
public import Mathlib.Tactic.NormNum.OfScientific
public import Mathlib.Tactic.Ring.RingNF
public import Definitions.Def_LeanPool_BooleanIsoperimetry_Harper
public import Theorems.Thm_BooleanIsoperimetry_harper_bc_min_case_le
public import Theorems.Thm_BooleanIsoperimetry_harper_bc_min_case_gt
public import Theorems.Thm_BooleanIsoperimetry_H_zero
public import Theorems.Thm_BooleanIsoperimetry_boundaryCost_comm
public import Theorems.Thm_BooleanIsoperimetry_boundaryCost_eq_case_gt
public import Theorems.Thm_BooleanIsoperimetry_boundaryCost_eq_case_le
public import Theorems.Thm_BooleanIsoperimetry_canonical_boundaryCost_eq_H_add
public import Theorems.Thm_BooleanIsoperimetry_harper_bc_min_q_zero_core
public import Theorems.Thm_BooleanIsoperimetry_mem_neighborhood_iff
attribute [local simp] BooleanIsoperimetry.mem_neighborhood_iff



set_option autoImplicit true
@[expose] public section
public section
open scoped BigOperators
open BooleanIsoperimetry
namespace BooleanIsoperimetry
theorem _root_.solution (n : ℕ)
    (ih : ∀ m, m < n → ∀ x y, x ≤ 2 ^ m → y ≤ 2 ^ m →
            H (m + 1) (x + y) ≤ max (H m x) y + max (H m y) x)
    {a b p q : ℕ}
    (ha : a ≤ 2 ^ n) (hb : b ≤ 2 ^ n) (hp : p ≤ 2 ^ n) (hq : q ≤ 2 ^ n)
    (hpq : p + q = a + b) (hcasc : CascadeSplit n (a + b) p q) :
    max (H n p) q + max (H n q) p ≤ max (H n a) b + max (H n b) a := by
  cases le_total b a with
  | inl hb_le_a =>
    by_cases hq_pos : 1 ≤ q
    · rw [canonical_boundaryCost_eq_H_add hp hq hq_pos hcasc]
      by_cases hcase : a ≤ H n b
      · rw [boundaryCost_eq_case_le ha hb_le_a hcase]
        exact harper_bc_min_case_le n ih ha hb hp hq hq_pos hb_le_a hcase hpq hcasc
      · push Not at hcase
        rw [boundaryCost_eq_case_gt ha hb_le_a hcase]
        exact harper_bc_min_case_gt n ih ha hb hp hq hq_pos hb_le_a hcase hpq hcasc
    · push Not at hq_pos
      have hq0 : q = 0 := by omega
      subst hq0
      have hpq_zero : p = a + b := by omega
      have hmax1 : max (H n p) 0 = H n p := max_eq_left (Nat.zero_le _)
      have hmax2 : max (H n 0) p = p := by rw [H_zero n]; exact max_eq_right (Nat.zero_le _)
      rw [hmax1, hmax2]
      exact harper_bc_min_q_zero_core n ha hb hp hb_le_a hpq_zero hcasc
  | inr ha_le_b =>
    rw [boundaryCost_comm n a b]
    have hpq_symm : p + q = b + a := by omega
    have hcasc_symm : CascadeSplit n (b + a) p q := by
      simpa [Nat.add_comm] using hcasc
    by_cases hq_pos : 1 ≤ q
    · rw [canonical_boundaryCost_eq_H_add hp hq hq_pos hcasc]
      by_cases hcase : b ≤ H n a
      · rw [boundaryCost_eq_case_le hb ha_le_b hcase]
        exact harper_bc_min_case_le n ih hb ha hp hq hq_pos ha_le_b hcase hpq_symm hcasc_symm
      · push Not at hcase
        rw [boundaryCost_eq_case_gt hb ha_le_b hcase]
        exact harper_bc_min_case_gt n ih hb ha hp hq hq_pos ha_le_b hcase hpq_symm hcasc_symm
    · push Not at hq_pos
      have hq0 : q = 0 := by omega
      subst hq0
      have hpq_zero : p = b + a := by omega
      have hmax1 : max (H n p) 0 = H n p := max_eq_left (Nat.zero_le _)
      have hmax2 : max (H n 0) p = p := by rw [H_zero n]; exact max_eq_right (Nat.zero_le _)
      rw [hmax1, hmax2]
      exact harper_bc_min_q_zero_core n hb ha hp ha_le_b hpq_zero hcasc_symm
end BooleanIsoperimetry
