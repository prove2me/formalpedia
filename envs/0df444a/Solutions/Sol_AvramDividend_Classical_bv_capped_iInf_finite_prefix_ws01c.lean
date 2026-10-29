-- Prove2me | solution 1 for AvramDividend.Classical.bv_capped_iInf_finite_prefix_ws01c
-- status  : ACCEPTED   (prove)
-- author  : @fizzyinc3
-- created : 2026-10-28T22:19:14.272204+00:00
-- url     : https://prove2.me/submissions/5931b37c-73a9-4be1-83b0-5d1666b7f1d4

import Mathlib
open Filter Set Order
open scoped NNReal ENNReal
theorem solution
    {α : Type*} [CompleteLinearOrder α]
    (v : ℕ → α) (T : α) (M : ℕ)
    (hTail : ∀ k : ℕ, M < k → T ≤ v k) :
    (⨅ k : ℕ, v k) ⊓ T =
      (⨅ (k : ℕ) (_ : k ≤ M), v k) ⊓ T := by
  apply le_antisymm
  · exact inf_le_inf_right T (le_iInf₂ fun k _ => iInf_le v k)
  · refine le_inf (le_iInf fun k => ?_) inf_le_right
    by_cases h : k ≤ M
    · exact inf_le_left.trans (iInf₂_le k h)
    · exact inf_le_right.trans (hTail k (lt_of_not_ge h))
