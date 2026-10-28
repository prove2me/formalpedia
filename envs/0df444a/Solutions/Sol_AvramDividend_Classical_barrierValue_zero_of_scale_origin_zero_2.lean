-- Prove2me | solution 2 for AvramDividend.Classical.barrierValue_zero_of_scale_origin_zero
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-10-25T22:11:16.173996+00:00
-- url     : https://prove2.me/submissions/a105a736-8da2-4e48-a7de-8b5247fe2bc4

import Mathlib.Data.EReal.Basic
import Definitions.Def_AvramDividend_Classical_ScaleFunction

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open AvramDividend.Classical
open scoped ENNReal

/-- A zero initial scale value annihilates the zero-barrier analytic quotient. -/
theorem solution
    (W : ℝ → ℝ) (hzero : W 0 = 0) :
    barrierValue W 0 0 = 0 := by
  simp [barrierValue, scaleDeriv, divE, hzero]
