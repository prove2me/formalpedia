-- Prove2me | solution 1 for AvramDividend.Classical.avram_bvb_obstruction_tenth_horizon_strict_prefix_contains_eight_hundredths
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-15T07:37:59.469196+00:00
-- url     : https://prove2.me/submissions/3c861061-256b-4dc7-9eb3-a820a63e2d95

import Mathlib
set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open Real
theorem solution (n : ℕ) (hn : 4 ≤ n) :
      (2 / 25 : ℝ) < 1 / 10 - (1 / 10) / ((n : ℝ) + 2) := by
  have hnn : (4 : ℝ) ≤ n := by exact_mod_cast hn
  have hp : 0 < (n : ℝ) + 2 := by positivity
  have hd : (1 / 10 : ℝ) / ((n : ℝ) + 2) ≤ 1 / 60 := by
    apply (div_le_iff₀ hp).2
    nlinarith
  linarith
