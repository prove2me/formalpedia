-- Prove2me | solution 1 for BooleanIsoperimetry.harper_extremal_step_nested
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-22T07:58:19.63394+00:00
-- url     : https://prove2.me/submissions/1906fbe3-f607-46b7-b8f7-cb0da9316e73

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
public import Theorems.Thm_BooleanIsoperimetry_harper_extremal_step_nested_pos
public import Theorems.Thm_BooleanIsoperimetry_H_succ_cascade
public import Theorems.Thm_BooleanIsoperimetry_canonical_boundaryCost_eq_H_add
public import Theorems.Thm_BooleanIsoperimetry_cascade_p_le
public import Theorems.Thm_BooleanIsoperimetry_cascade_q_le
public import Theorems.Thm_BooleanIsoperimetry_harper_extremal_step_nested_q_zero


set_option autoImplicit true
@[expose] public section
public section
open scoped BigOperators
open BooleanIsoperimetry
namespace BooleanIsoperimetry
theorem _root_.solution (n : ℕ)
    (ih : ∀ m, m < n + 1 → ∀ x y, x ≤ 2 ^ m → y ≤ 2 ^ m →
            H (m + 1) (x + y) ≤ max (H m x) y + max (H m y) x)
    {a b p q p0 p1 q0 q1 a0 a1 b0 b1 : ℕ}
    (ha : a ≤ 2 ^ (n + 1)) (hb : b ≤ 2 ^ (n + 1))
    (hcasc : CascadeSplit (n + 1) (a + b) p q)
    (hp0 : p0 ≤ 2 ^ n) (hp1 : p1 ≤ 2 ^ n)
    (hq0 : q0 ≤ 2 ^ n) (hq1 : q1 ≤ 2 ^ n)
    (ha0 : a0 ≤ 2 ^ n) (ha1 : a1 ≤ 2 ^ n)
    (hb0 : b0 ≤ 2 ^ n) (hb1 : b1 ≤ 2 ^ n)
    (hp_split : CascadeSplit n p p0 p1)
    (hq_split : CascadeSplit n q q0 q1)
    (ha_split : CascadeSplit n a a0 a1)
    (hb_split : CascadeSplit n b b0 b1) :
    max (max (H n p0) p1 + max (H n p1) p0) q +
    max (max (H n q0) q1 + max (H n q1) q0) p ≤
    max (max (H n a0) a1 + max (H n a1) a0) b +
    max (max (H n b0) b1 + max (H n b1) b0) a := by
  by_cases hq_zero : q = 0
  · exact harper_extremal_step_nested_q_zero n ih ha hb hcasc hq_zero
      hp0 hp1 hq0 hq1 ha0 ha1 hb0 hb1
      hp_split hq_split ha_split hb_split
  · have hq_pos : 1 ≤ q := Nat.succ_le_of_lt (Nat.pos_of_ne_zero hq_zero)
    have hp : p ≤ 2 ^ (n + 1) := cascade_p_le hcasc
    have hq : q ≤ 2 ^ (n + 1) := cascade_q_le hcasc
    have hpos := harper_extremal_step_nested_pos n ih ha hb hcasc
    rw [← H_succ_cascade hp_split, ← H_succ_cascade hq_split,
        ← H_succ_cascade ha_split, ← H_succ_cascade hb_split]
    rw [canonical_boundaryCost_eq_H_add hp hq hq_pos hcasc]
    exact hpos
end BooleanIsoperimetry
