-- Prove2me | solution 1 for AvramDividend.Classical.avram_jump6_B_actual_canonical_grid_one_cell_width_le_v2
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-19T19:08:33.885177+00:00
-- url     : https://prove2.me/submissions/0bb4a295-5a5a-48b1-b563-05c85055cd36

import Mathlib
import Definitions.Def_AvramDividend_Classical_DividendStrategy
open MeasureTheory Set Filter AvramDividend.Classical
open scoped NNReal
noncomputable section
set_option autoImplicit false

theorem solution
    (j i : ℕ) (t : ℝ≥0) :
    let v : ℕ → ℝ≥0 :=
      fun k => min ((k : ℝ≥0) / ((j + 1 : ℕ) : ℝ≥0)) t
    v (i + 1) ≤ v i + (1 : ℝ≥0) / ((j + 1 : ℕ) : ℝ≥0) := by
  dsimp
  have hstep :
      ((i + 1 : ℕ) : ℝ≥0) / ((j + 1 : ℕ) : ℝ≥0) =
        (i : ℝ≥0) / ((j + 1 : ℕ) : ℝ≥0) +
          (1 : ℝ≥0) / ((j + 1 : ℕ) : ℝ≥0) := by
    push_cast
    ring
  rw [hstep]
  by_cases hi : (i : ℝ≥0) / ((j + 1 : ℕ) : ℝ≥0) ≤ t
  · rw [min_eq_left hi]
    exact min_le_left _ _
  · have ht : t ≤ (i : ℝ≥0) / ((j + 1 : ℕ) : ℝ≥0) :=
      le_of_not_ge hi
    rw [min_eq_right ht]
    exact (min_le_right _ _).trans (le_add_of_nonneg_right (by positivity))
