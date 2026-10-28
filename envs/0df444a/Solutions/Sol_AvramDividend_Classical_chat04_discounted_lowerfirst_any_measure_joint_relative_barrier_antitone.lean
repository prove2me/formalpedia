-- Prove2me | solution 1 for AvramDividend.Classical.chat04_discounted_lowerfirst_any_measure_joint_relative_barrier_antitone
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-10-24T12:06:21.476992+00:00
-- url     : https://prove2.me/submissions/329cd929-9961-416a-891e-7ea5d9edd6dc

import Mathlib.MeasureTheory.Integral.Lebesgue.Basic
import Definitions.Def_AvramDividend_Classical_TwoSidedExit
import Theorems.Thm_AvramDividend_Classical_chat04_pointwise_discounted_strict_lowerfirst_joint_relative_barrier_antitone

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open AvramDividend.Classical MeasureTheory
open scoped NNReal ENNReal

/-- Strict lower-first discounted ruin value decreases jointly with improving reserve and larger discount under every path law. -/
theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕) (μ : Measure Ω)
    (q₁ q₂ a b x y : ℝ) (hq₁ : 0 ≤ q₁) (hq : q₁ ≤ q₂)
    (hxy : x ≤ y) (hrel : b - y ≤ a - x) :
    (∫⁻ ω,
      if twoSidedExitDownTime X (-y) ω < twoSidedExitUpTime X (b - y) ω then
        ENNReal.ofReal (Real.exp
          (-(q₂ * ENNReal.toReal (twoSidedExitDownTime X (-y) ω))))
      else 0 ∂μ) ≤
    (∫⁻ ω,
      if twoSidedExitDownTime X (-x) ω < twoSidedExitUpTime X (a - x) ω then
        ENNReal.ofReal (Real.exp
          (-(q₁ * ENNReal.toReal (twoSidedExitDownTime X (-x) ω))))
      else 0 ∂μ) := by
  apply lintegral_mono
  intro ω
  exact chat04_pointwise_discounted_strict_lowerfirst_joint_relative_barrier_antitone
    X q₁ q₂ a b x y hq₁ hq hxy hrel ω
