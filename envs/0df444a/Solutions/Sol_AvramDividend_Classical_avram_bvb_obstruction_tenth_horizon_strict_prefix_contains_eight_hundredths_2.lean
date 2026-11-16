-- Prove2me | solution 2 for AvramDividend.Classical.avram_bvb_obstruction_tenth_horizon_strict_prefix_contains_eight_hundredths
-- status  : ACCEPTED   (prove)
-- author  : @lookeng
-- created : 2026-11-15T17:14:33.392227+00:00
-- url     : https://prove2.me/submissions/89c4eeed-3cf5-42b5-8def-20f22cc15bdb

import Mathlib
open Real

theorem solution (n : ℕ) (hn : 4 ≤ n) :
      (2 / 25 : ℝ) < 1 / 10 - (1 / 10) / ((n : ℝ) + 2) := by
  have h4 : (4 : ℝ) ≤ (n : ℝ) := by exact_mod_cast hn
  have hpos : (0 : ℝ) < (n : ℝ) + 2 := by linarith
  have key : (1 / 10 : ℝ) / ((n : ℝ) + 2) < 1 / 50 := by
    rw [div_lt_iff₀ hpos]
    linarith
  linarith
