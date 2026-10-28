-- Prove2me | solution 1 for AvramDividend.Classical.barrierValue_zero_of_derivZeroPlus_top
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-10-25T12:45:35.322944+00:00
-- url     : https://prove2.me/submissions/5a5a0f41-03fc-48d6-9faa-3dc8f8d4490f

import Mathlib.Data.EReal.Basic
import Definitions.Def_AvramDividend_Classical_ScaleFunction

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open AvramDividend.Classical
open scoped ENNReal

/-- Infinite right scale derivative makes the zero-barrier quotient vanish. -/
theorem solution
    (W : ℝ → ℝ) (hder : derivZeroPlus W = ⊤) :
    barrierValue W 0 0 = 0 := by
  simp [barrierValue, scaleDeriv, divE, hder]
