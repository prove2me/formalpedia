-- Prove2me | solution 1 for AvramDividend.Classical.chat04_joint_discounted_exit_any_measure_comparison
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-10-24T11:11:32.027852+00:00
-- url     : https://prove2.me/submissions/7b008725-7f8a-4c3b-b4fa-464373625064

import Mathlib.MeasureTheory.Integral.Lebesgue.Basic
import Definitions.Def_AvramDividend_Classical_TwoSidedExit
import Theorems.Thm_AvramDividend_Classical_chat04_pointwise_discounted_strict_exit_joint_relative_barrier_mono

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open AvramDividend.Classical MeasureTheory
open scoped NNReal ENNReal

/-- The samplewise joint reserve, barrier and discount comparison integrates against any measure. -/
theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕) (μ : Measure Ω)
    (q₁ q₂ a b x y : ℝ) (hq₁ : 0 ≤ q₁) (hq : q₁ ≤ q₂)
    (hxy : x ≤ y) (hrel : b - y ≤ a - x) :
    (∫⁻ ω,
      if twoSidedExitUpTime X (a - x) ω < twoSidedExitDownTime X (-x) ω then
        ENNReal.ofReal (Real.exp
          (-(q₂ * ENNReal.toReal (twoSidedExitUpTime X (a - x) ω))))
      else 0 ∂μ) ≤
    (∫⁻ ω,
      if twoSidedExitUpTime X (b - y) ω < twoSidedExitDownTime X (-y) ω then
        ENNReal.ofReal (Real.exp
          (-(q₁ * ENNReal.toReal (twoSidedExitUpTime X (b - y) ω))))
      else 0 ∂μ) := by
  apply lintegral_mono
  intro ω
  exact chat04_pointwise_discounted_strict_exit_joint_relative_barrier_mono
    X q₁ q₂ a b x y hq₁ hq hxy hrel ω
