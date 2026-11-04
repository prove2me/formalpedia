-- Prove2me | solution 1 for AvramDividend.Classical.avram_p2_a_zero_rate_uniform_selected_cell_unique
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-03T20:45:24.050012+00:00
-- url     : https://prove2.me/submissions/59cd1823-13d5-4872-ad3b-adb3c72ed7d7

import Mathlib
import Theorems.Thm_AvramDividend_Classical_avram_p2_a_zero_rate_uniform_halfopen_cell_unique_index
set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open Filter Topology AvramDividend.Classical
open scoped NNReal

/-- Every true jump selected by its original uniform half-open grid cell
has the unique cell index required by the source-grid jump-test limit. -/
theorem solution
    (T : ℝ≥0) (F : Finset ℝ≥0)
    (idx : ℝ≥0 → ℕ → ℕ)
    (hcell : ∀ t ∈ F, ∀ n,
      (idx t n : ℝ≥0) * (T / ((n : ℝ≥0) + 1)) < t ∧
      t ≤ (((idx t n + 1 : ℕ) : ℝ≥0) *
        (T / ((n : ℝ≥0) + 1)))) :
    ∀ (n i : ℕ), ∀ t ∈ F,
      (i : ℝ≥0) * (T / ((n : ℝ≥0) + 1)) < t ∧
      t ≤ (((i + 1 : ℕ) : ℝ≥0) * (T / ((n : ℝ≥0) + 1))) →
      i = idx t n := by
  intro n i t htF hcross
  exact avram_p2_a_zero_rate_uniform_halfopen_cell_unique_index
    t (T / ((n : ℝ≥0) + 1)) i (idx t n) hcross (hcell t htF n)
