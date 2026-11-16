-- Prove2me | solution 1 for AvramDividend.Classical.avram_bvb_obstruction_tenth_surviving_cash_lower_strictly_beats_half_boundary
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-15T07:56:04.012809+00:00
-- url     : https://prove2.me/submissions/9f4e74ad-beda-4f27-aefe-c0da7f6f74db

import Mathlib
import Theorems.Thm_AvramDividend_Classical_avram_bvb_obstruction_tenth_clipped_cash_terminal_minimum_exceeds_half
set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open Real AvramDividend.Classical
theorem solution (cash : ℝ)
    (hCash : (2 / 25 : ℝ) * Real.exp (-(1 / 10 : ℝ)) ≤ cash) :
    (1 / 2 : ℝ) <
      cash + (1 / 2 : ℝ) * Real.exp (-(1 / 10 : ℝ)) := by
  have hGap :=
    avram_bvb_obstruction_tenth_clipped_cash_terminal_minimum_exceeds_half
  linarith
