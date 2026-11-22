-- Prove2me | solution 1 for BooleanIsoperimetry.harper_nested_g_gt
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-22T07:59:28.129005+00:00
-- url     : https://prove2.me/submissions/0e44fc16-4d00-4304-a376-6e800ac58c5d

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
public import Theorems.Thm_BooleanIsoperimetry_harper_extremal_step
public import Theorems.Thm_BooleanIsoperimetry_H_ge_self
public import Theorems.Thm_BooleanIsoperimetry_canonical_boundaryCost_eq_H_add


set_option autoImplicit true
@[expose] public section
public section
open scoped BigOperators
open BooleanIsoperimetry
namespace BooleanIsoperimetry
theorem _root_.solution (n : ℕ)
    (ih : ∀ m, m < n + 1 → ∀ x y, x ≤ 2 ^ m → y ≤ 2 ^ m →
            H (m + 1) (x + y) ≤ max (H m x) y + max (H m y) x)
    {a b p q : ℕ}
    (ha : a ≤ 2 ^ (n + 1)) (hb : b ≤ 2 ^ (n + 1))
    (hp : p ≤ 2 ^ (n + 1)) (hq : q ≤ 2 ^ (n + 1))
    (hq_pos : 1 ≤ q)
    (hb_le_a : b ≤ a)
    (hcase : H (n + 1) b < a)
    (_ : p + q = a + b)
    (hcasc : CascadeSplit (n + 1) (a + b) p q) :
    H (n + 1) p + H (n + 1) q ≤ H (n + 1) a + a := by
  have hL := harper_extremal_step n ih ha hb hcasc
  rw [canonical_boundaryCost_eq_H_add hp hq hq_pos hcasc] at hL
  have hga : a ≤ H (n + 1) a := H_ge_self (n + 1) a ha
  have m1 : max (H (n + 1) a) b = H (n + 1) a := max_eq_left (le_trans hb_le_a hga)
  have m2 : max (H (n + 1) b) a = a := max_eq_right (le_of_lt hcase)
  rw [m1, m2] at hL
  exact hL
end BooleanIsoperimetry
