-- Prove2me | solution 1 for AvramDividend.Classical.avram_p3_main_original_finite_grid_C1_two_stage_error
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-04T09:21:16.879713+00:00
-- url     : https://prove2.me/submissions/f4048509-919c-4bf5-ba4e-d751e2a3760a

import Mathlib
import Theorems.Thm_AvramDividend_Classical_avram_p3_main_public_weighted_source_jump_taylor_error
import Theorems.Thm_AvramDividend_Classical_avram_p3_main_public_large_small_original_jump_translation_bound
set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open AvramDividend.Classical
open scoped BigOperators

/-- Original physical finite-grid increment versus the exact intrinsic jump
increment and C1 drift, retaining large/small source mark errors. -/
theorem solution
    (n : ℕ) (S : Finset ℕ) (f : ℝ → ℝ)
    (r z cont jump delta : ℕ → ℝ) (ε B K : ℝ)
    (hε : 0 ≤ ε) (hK : 0 ≤ K)
    (hstep : ∀ i, i < n → delta i = cont i - jump i)
    (hr : ∀ i, i < n → 0 ≤ r i ∧ r i ≤ 1)
    (htaylor : ∀ i, i < n →
      |f (z i + cont i) - f (z i) - deriv f (z i) * cont i| ≤
        ε * |cont i|)
    (hvar : (∑ i ∈ Finset.range n, |cont i|) ≤ B)
    (hlarge : ∀ i, i < n → i ∈ S →
      |f (z i + cont i - jump i) - f (z i - jump i)| ≤ K * |cont i| ∧
      |f (z i + cont i) - f (z i)| ≤ K * |cont i|)
    (hsmall : ∀ i, i < n → i ∉ S →
      |f (z i + cont i - jump i) - f (z i + cont i)| ≤ K * |jump i| ∧
      |f (z i - jump i) - f (z i)| ≤ K * |jump i|) :
    |∑ i ∈ Finset.range n,
      r i * ((f (z i + delta i) - f (z i)) -
        (f (z i - jump i) - f (z i)) -
        deriv f (z i) * cont i)| ≤
      ε * B + 2 * K * (∑ i ∈ Finset.range n,
        if i ∈ S then |cont i| else |jump i|) := by
  classical
  have hA := avram_p3_main_public_weighted_source_jump_taylor_error
    f n r z cont jump delta ε B hε hstep hr htaylor hvar
  have hB := avram_p3_main_public_large_small_original_jump_translation_bound
    n S f r z cont jump K hK hr hlarge hsmall
  have heq :
      (∑ i ∈ Finset.range n,
        r i * ((f (z i + delta i) - f (z i)) -
          (f (z i - jump i) - f (z i)) -
          deriv f (z i) * cont i)) =
      (∑ i ∈ Finset.range n,
        r i * ((f (z i + delta i) - f (z i)) -
          (f (z i + cont i - jump i) - f (z i + cont i)) -
          deriv f (z i) * cont i)) +
      (∑ i ∈ Finset.range n,
        r i * ((f (z i + cont i - jump i) - f (z i + cont i)) -
          (f (z i - jump i) - f (z i)))) := by
    rw [← Finset.sum_add_distrib]
    apply Finset.sum_congr rfl
    intro i hi
    ring
  rw [heq]
  exact (abs_add_le _ _).trans (add_le_add hA hB)
