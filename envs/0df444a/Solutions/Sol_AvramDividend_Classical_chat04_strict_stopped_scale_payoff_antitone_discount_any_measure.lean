-- Prove2me | solution 1 for AvramDividend.Classical.chat04_strict_stopped_scale_payoff_antitone_discount_any_measure
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-10-24T14:25:58.431107+00:00
-- url     : https://prove2.me/submissions/b1b113ff-7d2c-4447-b068-d7d5b205e8ec

import Mathlib.Data.ENNReal.Real
import Mathlib.MeasureTheory.Integral.Lebesgue.Basic
import Definitions.Def_AvramDividend_Classical_TwoSidedExit
import Theorems.Thm_AvramDividend_Classical_chat04_strict_stopped_exit_payoff_any_measure_factorisation
import Theorems.Thm_AvramDividend_Classical_chat04_strict_exit_lintegral_antitone_discount_any_measure

set_option pp.universes true

open MeasureTheory AvramDividend.Classical
open scoped NNReal ENNReal

set_option pp.explicit true
set_option pp.fullNames true

/-- The strict upper-first stopped q-scale payoff decreases as the discount
rate increases, under any path-space measure. -/
theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕) (μ : Measure Ω)
    (q₁ q₂ a x : ℝ) (hq : q₁ ≤ q₂) (hxa : x ≤ a)
    (W : ℝ → ℝ) :
    (∫⁻ ω,
      if twoSidedExitUpTime X (a - x) ω <
          twoSidedExitDownTime X (-x) ω then
        ENNReal.ofReal
          (Real.exp (-(q₂ * ENNReal.toReal
            (twoSidedExitUpTime X (a - x) ω)))) *
        ENNReal.ofReal
          (W (x + X.X (twoSidedExitUpTime X (a - x) ω).toNNReal ω))
      else 0 ∂μ) ≤
    (∫⁻ ω,
      if twoSidedExitUpTime X (a - x) ω <
          twoSidedExitDownTime X (-x) ω then
        ENNReal.ofReal
          (Real.exp (-(q₁ * ENNReal.toReal
            (twoSidedExitUpTime X (a - x) ω)))) *
        ENNReal.ofReal
          (W (x + X.X (twoSidedExitUpTime X (a - x) ω).toNNReal ω))
      else 0 ∂μ) := by
  calc
    (∫⁻ ω,
      if twoSidedExitUpTime X (a - x) ω <
          twoSidedExitDownTime X (-x) ω then
        ENNReal.ofReal
          (Real.exp (-(q₂ * ENNReal.toReal
            (twoSidedExitUpTime X (a - x) ω)))) *
        ENNReal.ofReal
          (W (x + X.X (twoSidedExitUpTime X (a - x) ω).toNNReal ω))
      else 0 ∂μ) =
        (∫⁻ ω,
      if twoSidedExitUpTime X (a - x) ω <
          twoSidedExitDownTime X (-x) ω then
        ENNReal.ofReal
          (Real.exp (-(q₂ * ENNReal.toReal
            (twoSidedExitUpTime X (a - x) ω))))
      else 0 ∂μ) * ENNReal.ofReal (W a) :=
      chat04_strict_stopped_exit_payoff_any_measure_factorisation
        X μ q₂ a x hxa W
    _ ≤ (∫⁻ ω,
      if twoSidedExitUpTime X (a - x) ω <
          twoSidedExitDownTime X (-x) ω then
        ENNReal.ofReal
          (Real.exp (-(q₁ * ENNReal.toReal
            (twoSidedExitUpTime X (a - x) ω))))
      else 0 ∂μ) * ENNReal.ofReal (W a) :=
      mul_le_mul_of_nonneg_right
        (chat04_strict_exit_lintegral_antitone_discount_any_measure
          X μ q₁ q₂ a x hq)
        zero_le
    _ = (∫⁻ ω,
      if twoSidedExitUpTime X (a - x) ω <
          twoSidedExitDownTime X (-x) ω then
        ENNReal.ofReal
          (Real.exp (-(q₁ * ENNReal.toReal
            (twoSidedExitUpTime X (a - x) ω)))) *
        ENNReal.ofReal
          (W (x + X.X (twoSidedExitUpTime X (a - x) ω).toNNReal ω))
      else 0 ∂μ) :=
      (chat04_strict_stopped_exit_payoff_any_measure_factorisation
        X μ q₁ a x hxa W).symm
