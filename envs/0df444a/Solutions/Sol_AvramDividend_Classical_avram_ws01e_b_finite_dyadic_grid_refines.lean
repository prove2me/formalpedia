-- Prove2me | solution 1 for AvramDividend.Classical.avram_ws01e_b_finite_dyadic_grid_refines
-- status  : ACCEPTED   (prove)
-- author  : @fizzyinc3
-- created : 2026-10-28T01:01:19.419994+00:00
-- url     : https://prove2.me/submissions/7d2937ef-a7be-4ed2-b229-1b050e7e495a

import Mathlib
open scoped NNReal ENNReal

theorem solution (T : ℝ≥0) (n : ℕ)
    (k : Fin ((2 : ℕ) ^ n + 1)) :
    ∃ j : Fin ((2 : ℕ) ^ (n + 1) + 1),
      ((j.val : ℝ≥0) / (2 : ℝ≥0) ^ (n + 1)) * T =
      ((k.val : ℝ≥0) / (2 : ℝ≥0) ^ n) * T := by
  refine ⟨⟨2 * k.val, by have := k.isLt; rw [pow_succ]; omega⟩, ?_⟩
  simp only
  push_cast
  rw [pow_succ]
  congr 1
  field_simp
