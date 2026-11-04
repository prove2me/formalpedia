-- Prove2me | solution 1 for AvramDividend.Classical.avram_p2_a_zero_rate_original_uniform_selected_cells_eventually_injective
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-03T21:25:13.543872+00:00
-- url     : https://prove2.me/submissions/b304957a-5140-4ae5-8060-5d8c18589718

import Mathlib
import Theorems.Thm_AvramDividend_Classical_avram_p2_a_zero_rate_uniform_finite_selected_indices_injective
import Theorems.Thm_AvramDividend_Classical_avram_p2_a_zero_rate_selected_crossing_right_tendsto
import Theorems.Thm_AvramDividend_Classical_avram_p2_a_zero_rate_uniform_nnreal_width_tendsto_zero

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open Filter Topology AvramDividend.Classical
open scoped NNReal

/-- Distinct actual jump times eventually occupy different cells in the
original source's nonnegative uniform time grid. -/
theorem solution
    (T : ℝ≥0) (F : Finset ℝ≥0) (idx : ℝ≥0 → ℕ → ℕ)
    (hcell : ∀ t ∈ F, ∀ n,
      (idx t n : ℝ≥0) * (T / ((n : ℝ≥0) + 1)) < t ∧
      t ≤ (((idx t n + 1 : ℕ) : ℝ≥0) *
        (T / ((n : ℝ≥0) + 1)))) :
    ∀ᶠ n : ℕ in atTop,
      Set.InjOn (fun t => idx t n) (F : Set ℝ≥0) := by
  apply avram_p2_a_zero_rate_uniform_finite_selected_indices_injective F idx
    (fun n => T / ((n : ℝ≥0) + 1))
  intro t ht
  apply avram_p2_a_zero_rate_selected_crossing_right_tendsto t
    (fun n => (idx t n : ℝ≥0) * (T / ((n : ℝ≥0) + 1)))
    (fun n => (((idx t n + 1 : ℕ) : ℝ≥0) *
      (T / ((n : ℝ≥0) + 1))))
    (fun n => T / ((n : ℝ≥0) + 1))
  · exact hcell t ht
  · intro n
    simp only [Nat.cast_add, Nat.cast_one, add_mul, one_mul]
    exact le_refl _
  · exact avram_p2_a_zero_rate_uniform_nnreal_width_tendsto_zero T
