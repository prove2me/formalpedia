-- Prove2me | solution 1 for BooleanIsoperimetry.harper_step_le_canonical_sum
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-22T07:54:43.131434+00:00
-- url     : https://prove2.me/submissions/782f6583-4774-4772-bc5d-83c746b1d9fa

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
public import Theorems.Thm_BooleanIsoperimetry_harper_macaulay_window_le
public import Theorems.Thm_BooleanIsoperimetry_H_one
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
    (ih : ∀ m, m < n + 1 → ∀ x y, x ≤ 2 ^ m → y ≤ 2 ^ m →
            H (m + 1) (x + y) ≤ max (H m x) y + max (H m y) x)
    {a b p q : ℕ} (ha : a ≤ 2 ^ (n + 1)) (hb : b ≤ 2 ^ (n + 1))
    (hcasc : CascadeSplit (n + 1) (a + b) p q)
    (hba : b ≤ a) (hcase : a ≤ H (n + 1) b) :
    H (n + 1) p + H (n + 1) q ≤ H (n + 1) a + H (n + 1) b := by
  by_cases hq : q = 0
  · have htotal : a + b ≤ 1 := by
      simpa [hq] using cascade_split_q_zero_total_le_one (by simpa [hq] using hcasc)
    have hb_zero : b = 0 := by omega
    subst b
    have ha_val : a = 0 ∨ a = 1 := by omega
    rcases ha_val with rfl | rfl
    · have hp_val : p = 0 := by have hsum := cascade_split_add hcasc; omega
      simp [hq, hp_val]
    · have hp_val : p = 1 := by have hsum := cascade_split_add hcasc; omega
      simp [hq, hp_val, H_zero, H_one]
  · have hq_pos : 1 ≤ q := Nat.pos_of_ne_zero hq
    exact harper_macaulay_window_le n ih ha hb hcasc hq_pos hba hcase
end BooleanIsoperimetry
