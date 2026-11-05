-- Prove2me | solution 1 for AvramDividend.Classical.avram_p2_e_compensator_uniform_grid_width_tsub
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-04T17:03:40.491274+00:00
-- url     : https://prove2.me/submissions/0998417e-2de9-4c72-90e2-b777f40741f1

import Mathlib.Data.NNReal.Defs

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open scoped NNReal

/-- Right endpoint minus strict-left endpoint is exactly the physical uniform cell width. -/
theorem solution (i : ℕ) (δ : ℝ≥0) :
    (((i + 1 : ℕ) : ℝ≥0) * δ) - ((i : ℝ≥0) * δ) = δ := by
  have hadd : (((i + 1 : ℕ) : ℝ≥0) * δ) =
      ((i : ℝ≥0) * δ) + δ := by
    push_cast
    ring
  rw [hadd]
  exact add_tsub_cancel_left ((i : ℝ≥0) * δ) δ
