-- Prove2me | solution 1 for AvramDividend.Classical.avram_bvb_obstruction_tenth_clipped_cash_terminal_minimum_exceeds_half
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-15T07:44:40.934992+00:00
-- url     : https://prove2.me/submissions/bce543ea-fc2e-4820-a1b4-09a120e785c0

import Mathlib
set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open Real
theorem solution : (1 / 2 : ℝ) <
      (2 / 25 + 1 / 2) * Real.exp (-(1 / 10 : ℝ)) := by
  have he : (9 / 10 : ℝ) ≤ Real.exp (-(1 / 10 : ℝ)) := by
    have h := Real.add_one_le_exp (-(1 / 10 : ℝ))
    norm_num at h ⊢
    linarith
  nlinarith
