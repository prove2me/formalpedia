-- Prove2me | solution 3 for AvramDividend.Classical.barrierValue_zero_of_scale_origin_zero
-- status  : ACCEPTED   (prove)
-- author  : @fizzyinc3
-- created : 2026-10-25T22:11:18.304088+00:00
-- url     : https://prove2.me/submissions/b8ec61c8-2313-4616-968c-ad66cc1f63eb

import Definitions.Def_AvramDividend_Classical_ScaleFunction
import Mathlib.Data.Real.Basic

open AvramDividend.Classical
open AvramDividend.Classical

/-- The zero-barrier analytic value vanishes whenever the scale function starts at zero. -/
theorem solution
    (W : ℝ → ℝ) (hzero : W 0 = 0) : barrierValue W 0 0 = 0 := by 
  simp [barrierValue, divE, hzero]
