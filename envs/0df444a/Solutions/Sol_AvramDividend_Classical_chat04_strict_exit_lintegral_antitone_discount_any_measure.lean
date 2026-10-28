-- Prove2me | solution 1 for AvramDividend.Classical.chat04_strict_exit_lintegral_antitone_discount_any_measure
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-10-24T14:05:21.094994+00:00
-- url     : https://prove2.me/submissions/2c8a2981-5227-4e09-b956-d25b10ac3392

import Mathlib.Analysis.Complex.Exponential
import Mathlib.MeasureTheory.Integral.Lebesgue.Basic
import Mathlib.Data.ENNReal.Real
import Definitions.Def_AvramDividend_Classical_TwoSidedExit

set_option pp.universes true

open AvramDividend.Classical MeasureTheory
open scoped NNReal ENNReal

set_option pp.explicit true
set_option pp.fullNames true

/-- The strict discounted upper-before-ruin exit integral decreases as the
discount rate increases, under any measure on the path space. -/
theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕) (μ : Measure Ω)
    (q₁ q₂ a x : ℝ) (hq : q₁ ≤ q₂) :
    (∫⁻ ω,
      if twoSidedExitUpTime X (a - x) ω <
          twoSidedExitDownTime X (-x) ω then
        ENNReal.ofReal (Real.exp (-(q₂ * ENNReal.toReal
          (twoSidedExitUpTime X (a - x) ω))))
      else 0 ∂μ) ≤
    (∫⁻ ω,
      if twoSidedExitUpTime X (a - x) ω <
          twoSidedExitDownTime X (-x) ω then
        ENNReal.ofReal (Real.exp (-(q₁ * ENNReal.toReal
          (twoSidedExitUpTime X (a - x) ω))))
      else 0 ∂μ) := by
  apply lintegral_mono
  intro ω
  by_cases h : twoSidedExitUpTime X (a - x) ω <
      twoSidedExitDownTime X (-x) ω
  · simp only [if_pos h]
    apply ENNReal.ofReal_le_ofReal
    apply Real.exp_le_exp.mpr
    exact neg_le_neg (mul_le_mul_of_nonneg_right hq ENNReal.toReal_nonneg)
  · simp [h]
