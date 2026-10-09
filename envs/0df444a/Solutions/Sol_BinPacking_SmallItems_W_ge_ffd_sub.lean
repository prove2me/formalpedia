-- Prove2me | solution 1 for BinPacking.SmallItems.W_ge_ffd_sub
-- status  : ACCEPTED   (prove)
-- author  : @moona3k
-- created : 2026-10-04T18:51:12.107171+00:00
-- url     : https://prove2.me/submissions/31d056f9-83a0-4d50-b2e2-eccb2ce8a0d2

import Mathlib
import Definitions.Def_BinPacking_SmallItems_Model
import Definitions.Def_BinPacking_SmallItems_Weight
import Theorems.Thm_BinPacking_SmallItems_basic_weight_ge
import Theorems.Thm_BinPacking_SmallItems_w12_ge_basic_weight

set_option autoImplicit false

namespace BinPacking.SmallItems

/-- The two error sums of Claims 4.2.1 and 4.2.2 add up to `N - 2 - 1/2`. -/
theorem error_sum_aux (n : ℕ) :
    ∑ j ∈ Finset.Icc 2 (n + 2), (((j : ℝ) - 1) / (j : ℝ)) +
      ∑ j ∈ Finset.Icc 3 (n + 2), 1 / (j : ℝ) = (n : ℝ) + 1 - 1 / 2 := by
  induction n with
  | zero => norm_num
  | succ n ih =>
    have h1 : n + 1 + 2 = (n + 2) + 1 := by omega
    rw [h1, Finset.sum_Icc_succ_top (by omega : 2 ≤ (n + 2) + 1),
      Finset.sum_Icc_succ_top (by omega : 3 ≤ (n + 2) + 1)]
    have hpos : (0 : ℝ) < ((n + 2 + 1 : ℕ) : ℝ) := by positivity
    push_cast at hpos ⊢
    have : (((n : ℝ) + 2 + 1) - 1) / ((n : ℝ) + 2 + 1) + 1 / ((n : ℝ) + 2 + 1) = 1 := by
      field_simp
      ring
    linarith

end BinPacking.SmallItems

open BinPacking.SmallItems in
theorem solution (N : ℕ) (hN : 4 ≤ N) (L : List ℝ) (hL : IsList L)
    (hrange : ∀ a ∈ L, 1 / (N : ℝ) < a ∧ a ≤ 1 / 2) :
    W L ≥ (FFD L : ℝ) - (N : ℝ) + 2 := by
  obtain ⟨n, rfl⟩ : ∃ n, N = n + 3 := ⟨N - 3, by omega⟩
  have hbasic := basic_weight_ge (n + 3) hN L hL hrange
  have hsum := error_sum_aux n
  have hN1 : n + 3 - 1 = n + 2 := by omega
  rw [hN1] at hbasic
  rw [ge_iff_le]
  unfold W
  refine Finset.le_inf' _ _ fun σ hσ => ?_
  have h12 := w12_ge_basic_weight (n + 3) hN L hL hrange σ hσ
  rw [hN1] at h12
  push_cast
  linarith
