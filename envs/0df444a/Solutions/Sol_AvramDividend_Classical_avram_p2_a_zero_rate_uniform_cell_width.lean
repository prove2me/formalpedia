-- Prove2me | solution 1 for AvramDividend.Classical.avram_p2_a_zero_rate_uniform_cell_width
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-03T12:37:41.941881+00:00
-- url     : https://prove2.me/submissions/436f751a-2571-4619-b38a-c99ffd51ee40

import Mathlib
-- Preserve full pinned Mathlib for NNReal and real type notation.

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open scoped NNReal

/-- Every consecutive uniform NNReal time cell has exactly its prescribed
mesh width under truncated subtraction. -/
theorem solution (j : ℕ) (δ : ℝ≥0) :
    (((j + 1 : ℕ) : ℝ≥0) * δ) - ((j : ℝ≥0) * δ) = δ := by
  rw [Nat.cast_add, Nat.cast_one, add_mul, one_mul, add_tsub_cancel_left]
