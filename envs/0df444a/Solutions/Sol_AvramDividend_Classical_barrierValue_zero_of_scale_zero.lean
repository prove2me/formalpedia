-- Prove2me | solution 1 for AvramDividend.Classical.barrierValue_zero_of_scale_zero
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-10-24T19:37:17.364985+00:00
-- url     : https://prove2.me/submissions/bb3b9112-025a-4665-9694-3f3015fe2648

import Definitions.Def_AvramDividend_Classical_ScaleFunction

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open AvramDividend.Classical

/-- A vanishing scale origin makes the zero-barrier candidate zero. -/
theorem solution
    (W : ℝ → ℝ) (hW0 : W 0 = 0) :
    barrierValue W 0 0 = 0 := by
  simp [barrierValue, divE, hW0]
