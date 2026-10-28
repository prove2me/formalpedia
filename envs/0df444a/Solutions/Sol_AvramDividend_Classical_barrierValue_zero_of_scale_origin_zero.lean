-- Prove2me | solution 1 for AvramDividend.Classical.barrierValue_zero_of_scale_origin_zero
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-10-25T22:11:06.997132+00:00
-- url     : https://prove2.me/submissions/3fb3d004-0848-41b3-a8db-3422feed3286

import Definitions.Def_AvramDividend_Classical_ScaleFunction
import Mathlib.Data.Real.Basic

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open AvramDividend.Classical

/-- A vanishing scale-function numerator yields a zero barrier value. -/
theorem solution
    (W : ℝ → ℝ) (hzero : W 0 = 0) : barrierValue W 0 0 = 0 := by
  simp [barrierValue, scaleDeriv, divE, hzero]
