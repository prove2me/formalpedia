-- Prove2me | solution 1 for AvramDividend.Classical.chat04_twoSidedExitExpectation_le_one
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-10-23T14:15:29.129862+00:00
-- url     : https://prove2.me/submissions/8f46e8b2-4c93-4436-8352-8f32253e6365

import Mathlib.Analysis.Complex.Exponential
import Mathlib.MeasureTheory.Integral.Lebesgue.Basic
import Mathlib.Data.ENNReal.Real
import Definitions.Def_AvramDividend_Classical_TwoSidedExit

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open AvramDividend.Classical MeasureTheory
open scoped NNReal ENNReal

/-- Pointwise domination by one, including infinite stopping times. -/
theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕) (q a x : ℝ) (hq : 0 ≤ q) :
    twoSidedExitExpectation X q a x ≤ 1 := by
  letI : IsProbabilityMeasure P := X.isProbability
  unfold twoSidedExitExpectation
  calc
    (∫⁻ ω, if twoSidedExitUpTime X (a - x) ω <
        twoSidedExitDownTime X (-x) ω then
          ENNReal.ofReal (Real.exp (-(q * ENNReal.toReal
            (twoSidedExitUpTime X (a - x) ω)))) else 0 ∂P) ≤
        (∫⁻ _ω, (1 : ℝ≥0∞) ∂P) := by
      apply lintegral_mono
      intro ω
      change (if twoSidedExitUpTime X (a - x) ω <
          twoSidedExitDownTime X (-x) ω then
          ENNReal.ofReal (Real.exp (-(q * ENNReal.toReal
            (twoSidedExitUpTime X (a - x) ω)))) else 0) ≤ (1 : ℝ≥0∞)
      by_cases h : twoSidedExitUpTime X (a - x) ω <
          twoSidedExitDownTime X (-x) ω
      · simp only [if_pos h]
        have hmul : 0 ≤ q * ENNReal.toReal (twoSidedExitUpTime X (a - x) ω) :=
          mul_nonneg hq ENNReal.toReal_nonneg
        have hexp : Real.exp (-(q * ENNReal.toReal
            (twoSidedExitUpTime X (a - x) ω))) ≤ 1 :=
          Real.exp_le_one_iff.mpr (neg_nonpos.mpr hmul)
        simpa only [ENNReal.ofReal_one] using ENNReal.ofReal_le_ofReal hexp
      · simp [h]
    _ = 1 := by simp
