-- Prove2me | solution 1 for AvramDividend.Classical.vcstar_eq_zero_of_neg
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-10-07T22:51:30.939472+00:00
-- url     : https://prove2.me/submissions/3e4fdf65-a8ae-48ab-9b8b-9b84272b84dc

import Mathlib
import Definitions.Def_AvramDividend_Classical_ScaleFunction

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open AvramDividend.Classical

theorem solution (W : ℝ → ℝ) (x : ℝ) (hx : x < 0) :
    vcstar W x = 0 := by
  simp [vcstar, barrierValue, hx]
