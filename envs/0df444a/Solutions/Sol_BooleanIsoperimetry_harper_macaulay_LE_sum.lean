-- Prove2me | solution 1 for BooleanIsoperimetry.harper_macaulay_LE_sum
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-22T07:52:01.279562+00:00
-- url     : https://prove2.me/submissions/6a9e47a6-0e68-4d66-8b6c-29586871588d

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
public import Theorems.Thm_BooleanIsoperimetry_harper_macaulay_LE_sum_q_zero
public import Theorems.Thm_BooleanIsoperimetry_harper_macaulay_LE_sum_pos

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
    (hcasc : CascadeSplit (n + 1) (a + b) p q)
    (hba : b ≤ a) (hcase : a ≤ H (n + 1) b) :
    H (n + 1) p + H (n + 1) q ≤ H (n + 1) a + H (n + 1) b := by
  by_cases hq_zero : q = 0
  · subst hq_zero
    exact harper_macaulay_LE_sum_q_zero n hcasc hba
  · exact harper_macaulay_LE_sum_pos n ih ha hb hcasc (Nat.pos_of_ne_zero hq_zero) hba hcase
end BooleanIsoperimetry
