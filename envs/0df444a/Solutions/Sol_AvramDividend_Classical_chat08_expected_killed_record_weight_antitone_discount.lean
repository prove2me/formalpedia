-- Prove2me | solution 1 for AvramDividend.Classical.chat08_expected_killed_record_weight_antitone_discount
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-10-23T23:22:33.537842+00:00
-- url     : https://prove2.me/submissions/b85260b0-696d-4df3-b8d4-709731829960

import Mathlib.Analysis.Complex.Exponential
import Mathlib.MeasureTheory.Integral.Lebesgue.Basic
import Definitions.Def_AvramDividend_Classical_ReflectionBarrier
import Definitions.Def_AvramDividend_Classical_TwoSidedExit

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open AvramDividend.Classical MeasureTheory Set
open scoped NNReal ENNReal

/-! The expected killed strict first-record payment decreases with its discount parameter. -/
theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {ℱ : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P ℱ) (a c h q₁ q₂ : ℝ)
    (hh : 0 ≤ h) (hq : q₁ ≤ q₂) :
    (∫⁻ ω, (if twoSidedExitUpTime X c ω < barrierRuinTime X a ω then
       ENNReal.ofReal (h * Real.exp (-(q₂ * (twoSidedExitUpTime X c ω).toReal)))
     else 0) ∂P) ≤
    (∫⁻ ω, (if twoSidedExitUpTime X c ω < barrierRuinTime X a ω then
       ENNReal.ofReal (h * Real.exp (-(q₁ * (twoSidedExitUpTime X c ω).toReal)))
     else 0) ∂P) := by
  apply lintegral_mono
  intro ω
  by_cases he : twoSidedExitUpTime X c ω < barrierRuinTime X a ω
  · simp only [if_pos he]
    have ht : 0 ≤ (twoSidedExitUpTime X c ω).toReal := ENNReal.toReal_nonneg
    have hm : q₁ * (twoSidedExitUpTime X c ω).toReal ≤
        q₂ * (twoSidedExitUpTime X c ω).toReal :=
      mul_le_mul_of_nonneg_right hq ht
    have he' : Real.exp (-(q₂ * (twoSidedExitUpTime X c ω).toReal)) ≤
        Real.exp (-(q₁ * (twoSidedExitUpTime X c ω).toReal)) :=
      Real.exp_le_exp_of_le (neg_le_neg hm)
    exact ENNReal.ofReal_le_ofReal (mul_le_mul_of_nonneg_left he' hh)
  · simp only [if_neg he, le_refl]
