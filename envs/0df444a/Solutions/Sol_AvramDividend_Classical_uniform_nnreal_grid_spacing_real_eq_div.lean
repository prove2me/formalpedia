-- Prove2me | solution 1 for AvramDividend.Classical.uniform_nnreal_grid_spacing_real_eq_div
-- status  : ACCEPTED   (prove)
-- author  : @fizzyinc3
-- created : 2026-10-26T15:23:36.574457+00:00
-- url     : https://prove2.me/submissions/ba1c46ae-bbda-40b5-bf18-8b1acbae9d28

import Mathlib
open scoped NNReal

theorem solution
    (T δ : ℝ≥0) (N : ℕ) (hN : 0 < N)
    (hTotal : (N : ℝ≥0) * δ = T) :
    (δ : ℝ) = (T : ℝ) / (N : ℝ) := by
  rw [← hTotal]; push_cast
  have : (N : ℝ) ≠ 0 := by exact_mod_cast hN.ne'
  field_simp
