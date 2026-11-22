-- Prove2me | solution 1 for BooleanIsoperimetry.harper_subadd_le_cascade_pos_succ_nested
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-22T08:01:10.594367+00:00
-- url     : https://prove2.me/submissions/60abccac-a68d-4ac3-a4f7-32e28e86e75d

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
public import Theorems.Thm_BooleanIsoperimetry_harper_subadd_le_cascade_pos_succ_nested_core
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
    (hcase : a ≤ max (H n b0) b1 + max (H n b1) b0)
    (hpq : p + q = a + b)
    (hcasc : CascadeSplit (n + 1) (a + b) p q)
    (hp0 : p0 ≤ 2 ^ n) (hp1 : p1 ≤ 2 ^ n)
    (hq0 : q0 ≤ 2 ^ n) (hq1 : q1 ≤ 2 ^ n)
    (ha0 : a0 ≤ 2 ^ n) (ha1 : a1 ≤ 2 ^ n)
    (hb0 : b0 ≤ 2 ^ n) (hb1 : b1 ≤ 2 ^ n)
    (hp_split : CascadeSplit n p p0 p1)
    (hq_split : CascadeSplit n q q0 q1)
    (ha_split : CascadeSplit n a a0 a1)
    (hb_split : CascadeSplit n b b0 b1) :
    max (H n p0) p1 + max (H n p1) p0 +
        (max (H n q0) q1 + max (H n q1) q0) ≤
      max (H n a0) a1 + max (H n a1) a0 +
        (max (H n b0) b1 + max (H n b1) b0) := by
  rw [H_succ_cascade_expand hp_split hp0]
  rw [H_succ_cascade_expand hq_split hq0]
  rw [H_succ_cascade_expand ha_split ha0]
  rw [H_succ_cascade_expand hb_split hb0]
  have hcase_rewritten : a ≤ H n b0 + if 1 ≤ b1 then H n b1 else b0 := by
    rwa [← H_succ_cascade_expand hb_split hb0]
  exact harper_subadd_le_cascade_pos_succ_nested_core n ih ha hb hp hq hq_pos hb_le_a
    hcase_rewritten hpq hcasc hp0 hp1 hq0 hq1 ha0 ha1 hb0 hb1 hp_split hq_split ha_split hb_split
end BooleanIsoperimetry
