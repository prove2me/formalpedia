-- Prove2me | solution 1 for AvramDividend.Classical.avram_p2_h_cadlag_uniform_right_closed_cell_real_width
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-03T19:59:58.676346+00:00
-- url     : https://prove2.me/submissions/0b083eff-2fe6-4c32-8498-da74f89c390f

import Mathlib

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open Set Filter Topology
open scoped NNReal

/-- The real-coordinate width of every original right-closed
uniform cell is exactly T/(n+1), independently of the cell index. -/
theorem solution
    (T : ℝ≥0) (n j : ℕ) :
    (((((j + 1 : ℕ) : ℝ≥0) * (T / ((n : ℝ≥0) + 1))) : ℝ) -
      (((j : ℝ≥0) * (T / ((n : ℝ≥0) + 1))) : ℝ)) =
    (T : ℝ) / ((n : ℝ) + 1) := by
  have hcell (δ : ℝ≥0) :
      (((((j + 1 : ℕ) : ℝ≥0) * δ) : ℝ) -
        (((j : ℝ≥0) * δ) : ℝ)) = (δ : ℝ) := by
    simp only [Nat.cast_add, Nat.cast_one, add_mul, one_mul]
    push_cast
    ring
  simpa only [NNReal.coe_div, NNReal.coe_add, NNReal.coe_one,
    NNReal.coe_natCast] using hcell (T / ((n : ℝ≥0) + 1))
