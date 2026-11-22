-- Prove2me | solution 1 for BooleanIsoperimetry.harper_subadd_gt
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-22T08:01:58.937247+00:00
-- url     : https://prove2.me/submissions/e6ae828f-47c7-4c4d-9a7e-14618def9811

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
public import Theorems.Thm_BooleanIsoperimetry_harper_subadd_gt_cascade_pos
public import Theorems.Thm_BooleanIsoperimetry_H_succ_cascade
public import Theorems.Thm_BooleanIsoperimetry_H_zero
public import Theorems.Thm_BooleanIsoperimetry_boundaryCost_eq_case_gt
public import Theorems.Thm_BooleanIsoperimetry_canonical_boundaryCost_eq_H_add
public import Theorems.Thm_BooleanIsoperimetry_exists_cascade_split
public import Theorems.Thm_BooleanIsoperimetry_harper_bc_min_q_zero_core


set_option autoImplicit true
@[expose] public section
public section
open scoped BigOperators
open BooleanIsoperimetry
namespace BooleanIsoperimetry
theorem _root_.solution
    (n : ℕ)
    (ih : ∀ m, m < n → ∀ x y, x ≤ 2 ^ m → y ≤ 2 ^ m →
            H (m + 1) (x + y) ≤ max (H m x) y + max (H m y) x)
    {a b : ℕ}
    (ha : a ≤ 2 ^ n) (hb : b ≤ 2 ^ n)
    (hb_le_a : b ≤ a) (hcase : H n b < a) :
    H (n + 1) (a + b) ≤ H n a + a := by
  have hab : a + b ≤ 2 ^ (n + 1) := by
    calc a + b ≤ 2 ^ n + 2 ^ n := Nat.add_le_add ha hb
      _ = 2 * 2 ^ n := by omega
      _ = 2 ^ (n + 1) := by ring
  obtain ⟨p, q, hp, hq, hpq, hcasc⟩ := exists_cascade_split n (a + b) hab
  rw [H_succ_cascade hcasc]
  by_cases hq_pos : 1 ≤ q
  · rw [canonical_boundaryCost_eq_H_add hp hq hq_pos hcasc]
    exact harper_subadd_gt_cascade_pos n ih ha hb hp hq hq_pos hb_le_a hcase hpq hcasc
  · push Not at hq_pos
    have hq0 : q = 0 := by omega
    subst hq0
    have hpq_zero : p = a + b := by omega
    have hmax1 : max (H n p) 0 = H n p := max_eq_left (Nat.zero_le _)
    have hmax2 : max (H n 0) p = p := by rw [H_zero n]; exact max_eq_right (Nat.zero_le _)
    rw [hmax1, hmax2]
    have h_q_zero := harper_bc_min_q_zero_core n ha hb hp hb_le_a hpq_zero hcasc
    have h_bc := boundaryCost_eq_case_gt ha hb_le_a hcase
    omega
end BooleanIsoperimetry
