-- Prove2me | solution 1 for AvramDividend.Classical.chat04_strict_exit_discount_zero_of_negative_reserve
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-10-23T16:28:04.023005+00:00
-- url     : https://prove2.me/submissions/e69a5df1-5c5f-4feb-a0e2-7a569b2c32bc

import Mathlib.MeasureTheory.Integral.Lebesgue.Basic
import Definitions.Def_AvramDividend_Classical_TwoSidedExit

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open AvramDividend.Classical MeasureTheory Set
open scoped NNReal ENNReal

/-- Strict upward exit before ruin has zero discounted expectation from negative reserve. -/
theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕) (q a x : ℝ) (hx : x < 0) :
    twoSidedExitExpectation X q a x = 0 := by
  have hDownZero (ω : Ω) : twoSidedExitDownTime X (-x) ω = 0 := by
    have hAtZero : X.X (0 : ℝ≥0) ω < -x := by
      have hneg : 0 < -x := neg_pos.mpr hx
      simpa only [X.X_zero ω] using hneg
    unfold twoSidedExitDownTime
    apply le_antisymm
    · exact iInf₂_le (0 : ℝ≥0) hAtZero
    · exact bot_le
  simp [twoSidedExitExpectation, hDownZero]
