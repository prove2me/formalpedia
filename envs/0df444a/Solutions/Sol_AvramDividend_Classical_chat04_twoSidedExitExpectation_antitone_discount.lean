-- Prove2me | solution 1 for AvramDividend.Classical.chat04_twoSidedExitExpectation_antitone_discount
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-10-23T14:15:53.351902+00:00
-- url     : https://prove2.me/submissions/a11514f1-d5a4-4ee5-84ed-f49f963b7ec5

import Mathlib.Analysis.Complex.Exponential
import Mathlib.MeasureTheory.Integral.Lebesgue.Basic
import Mathlib.Data.ENNReal.Real
import Definitions.Def_AvramDividend_Classical_TwoSidedExit

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open AvramDividend.Classical MeasureTheory
open scoped NNReal ENNReal

/-- The exact killed strict exit expectation is antitone in discount. -/
theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (q₁ q₂ a x : ℝ) (hq : q₁ ≤ q₂) :
    twoSidedExitExpectation X q₂ a x ≤
      twoSidedExitExpectation X q₁ a x := by
  unfold twoSidedExitExpectation
  apply lintegral_mono
  intro ω
  change (if twoSidedExitUpTime X (a - x) ω <
      twoSidedExitDownTime X (-x) ω then
        ENNReal.ofReal (Real.exp (-(q₂ * ENNReal.toReal
          (twoSidedExitUpTime X (a - x) ω)))) else 0) ≤
    (if twoSidedExitUpTime X (a - x) ω <
      twoSidedExitDownTime X (-x) ω then
        ENNReal.ofReal (Real.exp (-(q₁ * ENNReal.toReal
          (twoSidedExitUpTime X (a - x) ω)))) else 0)
  by_cases h : twoSidedExitUpTime X (a - x) ω <
      twoSidedExitDownTime X (-x) ω
  · simp only [if_pos h]
    apply ENNReal.ofReal_le_ofReal
    apply Real.exp_le_exp.mpr
    exact neg_le_neg (mul_le_mul_of_nonneg_right hq ENNReal.toReal_nonneg)
  · simp [h]
