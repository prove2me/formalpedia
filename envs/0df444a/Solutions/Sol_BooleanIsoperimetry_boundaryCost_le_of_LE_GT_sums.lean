-- Prove2me | solution 1 for BooleanIsoperimetry.boundaryCost_le_of_LE_GT_sums
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-22T07:52:00.286287+00:00
-- url     : https://prove2.me/submissions/4dcf87dc-4c89-4a0b-9987-8187f71e20f3

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
public import Theorems.Thm_BooleanIsoperimetry_cascade_split_q_zero_total_le_one
public import Theorems.Thm_BooleanIsoperimetry_harper_macaulay_LE_sum_pos
public import Theorems.Thm_BooleanIsoperimetry_harper_macaulay_GT_sum
public import Theorems.Thm_BooleanIsoperimetry_H_ge_self
public import Theorems.Thm_BooleanIsoperimetry_canonical_boundaryCost_eq_H_add
public import Theorems.Thm_BooleanIsoperimetry_cascade_p_le
public import Theorems.Thm_BooleanIsoperimetry_cascade_q_le
public import Theorems.Thm_BooleanIsoperimetry_cascade_split_add


set_option autoImplicit true
@[expose] public section
public section
open scoped BigOperators
open BooleanIsoperimetry
namespace BooleanIsoperimetry
theorem _root_.solution (n : ℕ)
    (ih : ∀ m, m < n + 1 → ∀ x y, x ≤ 2 ^ m → y ≤ 2 ^ m →
            H (m + 1) (x + y) ≤ max (H m x) y + max (H m y) x)
    {a b p q : ℕ} (ha : a ≤ 2 ^ (n + 1)) (_hb : b ≤ 2 ^ (n + 1))
    (hcasc : CascadeSplit (n + 1) (a + b) p q) (hba : b ≤ a) :
    max (H (n + 1) p) q + max (H (n + 1) q) p ≤
      max (H (n + 1) a) b + max (H (n + 1) b) a := by
  have hp_cap : p ≤ 2 ^ (n + 1) := cascade_p_le hcasc
  have hq_cap : q ≤ 2 ^ (n + 1) := cascade_q_le hcasc
  by_cases hq_zero : q = 0
  · subst hq_zero
    have htot : a + b ≤ 1 := cascade_split_q_zero_total_le_one hcasc
    have hb0 : b = 0 := by omega
    subst hb0
    have ha_eq_p : a = p := by
      have hsum := cascade_split_add hcasc
      omega
    subst ha_eq_p
    exact le_rfl
  · have hq_pos : 1 ≤ q := Nat.pos_of_ne_zero hq_zero
    rw [canonical_boundaryCost_eq_H_add hp_cap hq_cap hq_pos hcasc]
    by_cases hcase : a ≤ H (n + 1) b
    · have hbHa : b ≤ H (n + 1) a := le_trans hba (H_ge_self (n + 1) a ha)
      rw [max_eq_left hbHa, max_eq_left hcase]
      exact harper_macaulay_LE_sum_pos n ih ha _hb hcasc hq_pos hba hcase
    · push Not at hcase
      have hbHa : b ≤ H (n + 1) a := le_trans hba (H_ge_self (n + 1) a ha)
      rw [max_eq_left hbHa, max_eq_right (le_of_lt hcase)]
      exact harper_macaulay_GT_sum n ih ha _hb hcasc hq_pos hba hcase
end BooleanIsoperimetry
