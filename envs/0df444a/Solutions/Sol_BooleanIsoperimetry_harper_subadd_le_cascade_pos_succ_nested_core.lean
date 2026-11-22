-- Prove2me | solution 1 for BooleanIsoperimetry.harper_subadd_le_cascade_pos_succ_nested_core
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-22T08:00:13.545801+00:00
-- url     : https://prove2.me/submissions/12b699a7-2733-4aa1-ad8d-fc0ff7eb39cb

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
public import Theorems.Thm_BooleanIsoperimetry_harper_nested_g_le
public import Theorems.Thm_BooleanIsoperimetry_H_succ_cascade
public import Theorems.Thm_BooleanIsoperimetry_H_succ_cascade_expand


set_option autoImplicit true
@[expose] public section
public section
open scoped BigOperators
open BooleanIsoperimetry
namespace BooleanIsoperimetry
theorem _root_.solution
    (n : ℕ)
    (ih : ∀ m, m < n + 1 → ∀ x y, x ≤ 2 ^ m → y ≤ 2 ^ m →
            H (m + 1) (x + y) ≤ max (H m x) y + max (H m y) x)
    {a b p q p0 p1 q0 q1 a0 a1 b0 b1 : ℕ}
    (ha : a ≤ 2 ^ (n + 1)) (hb : b ≤ 2 ^ (n + 1))
    (hp : p ≤ 2 ^ (n + 1)) (hq : q ≤ 2 ^ (n + 1))
    (hq_pos : 1 ≤ q)
    (hb_le_a : b ≤ a)
    (hcase : a ≤ H n b0 + if 1 ≤ b1 then H n b1 else b0)
    (hpq : p + q = a + b)
    (hcasc : CascadeSplit (n + 1) (a + b) p q)
    (hp0 : p0 ≤ 2 ^ n) (_ : p1 ≤ 2 ^ n)
    (hq0 : q0 ≤ 2 ^ n) (_ : q1 ≤ 2 ^ n)
    (ha0 : a0 ≤ 2 ^ n) (_ : a1 ≤ 2 ^ n)
    (hb0 : b0 ≤ 2 ^ n) (_ : b1 ≤ 2 ^ n)
    (hp_split : CascadeSplit n p p0 p1)
    (hq_split : CascadeSplit n q q0 q1)
    (ha_split : CascadeSplit n a a0 a1)
    (hb_split : CascadeSplit n b b0 b1) :
    H n p0 + (if 1 ≤ p1 then H n p1 else p0) +
        (H n q0 + (if 1 ≤ q1 then H n q1 else q0)) ≤
      H n a0 + (if 1 ≤ a1 then H n a1 else a0) +
        (H n b0 + (if 1 ≤ b1 then H n b1 else b0)) := by
  have ep : H n p0 + (if 1 ≤ p1 then H n p1 else p0) = H (n + 1) p := by
    rw [← H_succ_cascade_expand hp_split hp0]; exact (H_succ_cascade hp_split).symm
  have eq' : H n q0 + (if 1 ≤ q1 then H n q1 else q0) = H (n + 1) q := by
    rw [← H_succ_cascade_expand hq_split hq0]; exact (H_succ_cascade hq_split).symm
  have ea : H n a0 + (if 1 ≤ a1 then H n a1 else a0) = H (n + 1) a := by
    rw [← H_succ_cascade_expand ha_split ha0]; exact (H_succ_cascade ha_split).symm
  have eb : H n b0 + (if 1 ≤ b1 then H n b1 else b0) = H (n + 1) b := by
    rw [← H_succ_cascade_expand hb_split hb0]; exact (H_succ_cascade hb_split).symm
  rw [eb] at hcase
  rw [ep, eq', ea, eb]
  exact harper_nested_g_le n ih ha hb hp hq hq_pos hb_le_a hcase hpq hcasc
end BooleanIsoperimetry
