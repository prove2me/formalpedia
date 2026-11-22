-- Prove2me | solution 1 for BooleanIsoperimetry.harper_macaulay_GT_sum
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-22T07:51:25.08753+00:00
-- url     : https://prove2.me/submissions/7ed53a8d-64a6-4dc1-8345-0d21f215864f

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
public import Theorems.Thm_BooleanIsoperimetry_harper_macaulay_exchange_step
public import Theorems.Thm_BooleanIsoperimetry_H_ge_self
public import Theorems.Thm_BooleanIsoperimetry_canonical_boundaryCost_eq_H_add
public import Theorems.Thm_BooleanIsoperimetry_cascade_p_le
public import Theorems.Thm_BooleanIsoperimetry_cascade_q_le


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
    (hq_pos : 1 ≤ q) (hba : b ≤ a) (hcase : H (n + 1) b < a) :
    H (n + 1) p + H (n + 1) q ≤ H (n + 1) a + a := by
  have hp_cap : p ≤ 2 ^ (n + 1) := cascade_p_le hcasc
  have hq_cap : q ≤ 2 ^ (n + 1) := cascade_q_le hcasc
  have hmax := harper_macaulay_exchange_step n ih ha hb hcasc
  have hbHa : b ≤ H (n + 1) a := le_trans hba (H_ge_self (n + 1) a ha)
  rw [canonical_boundaryCost_eq_H_add hp_cap hq_cap hq_pos hcasc,
      max_eq_left hbHa, max_eq_right (le_of_lt hcase)] at hmax
  exact hmax
end BooleanIsoperimetry
