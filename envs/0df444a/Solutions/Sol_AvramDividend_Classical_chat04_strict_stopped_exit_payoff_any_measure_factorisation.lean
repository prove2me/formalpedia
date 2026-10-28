-- Prove2me | solution 1 for AvramDividend.Classical.chat04_strict_stopped_exit_payoff_any_measure_factorisation
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-10-24T11:32:35.183764+00:00
-- url     : https://prove2.me/submissions/6d61070a-f4dc-486e-bf18-b5f6fb47a1e3

import Mathlib.MeasureTheory.Integral.Lebesgue.Add
import Mathlib.Analysis.Complex.Exponential
import Definitions.Def_AvramDividend_Classical_TwoSidedExit
import Theorems.Thm_AvramDividend_Classical_chat04_strict_upper_exit_scale_payoff
import Theorems.Thm_AvramDividend_Classical_chat03_exact_upperfirst_discount_integrand_measurable

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory AvramDividend.Classical
open scoped NNReal ENNReal

/-- The stopped upper-exit q-scale payoff factors under every path-space measure. -/
theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕) (μ : Measure Ω)
    (q a x : ℝ) (hxa : x ≤ a) (W : ℝ → ℝ) :
    (∫⁻ ω,
      if twoSidedExitUpTime X (a - x) ω <
          twoSidedExitDownTime X (-x) ω then
        ENNReal.ofReal
          (Real.exp (-(q * ENNReal.toReal (twoSidedExitUpTime X (a - x) ω)))) *
          ENNReal.ofReal
            (W (x + X.X (twoSidedExitUpTime X (a - x) ω).toNNReal ω))
      else 0 ∂μ) =
      (∫⁻ ω,
        if twoSidedExitUpTime X (a - x) ω <
            twoSidedExitDownTime X (-x) ω then
          ENNReal.ofReal
            (Real.exp (-(q * ENNReal.toReal (twoSidedExitUpTime X (a - x) ω))))
        else 0 ∂μ) * ENNReal.ofReal (W a) := by
  have hm : Measurable (fun ω : Ω =>
      if twoSidedExitUpTime X (a - x) ω <
          twoSidedExitDownTime X (-x) ω then
        ENNReal.ofReal
          (Real.exp (-(q * ENNReal.toReal (twoSidedExitUpTime X (a - x) ω))))
      else 0) :=
    chat03_exact_upperfirst_discount_integrand_measurable X (-x) (a - x) q
  calc
    _ = (∫⁻ ω,
        (if twoSidedExitUpTime X (a - x) ω <
                twoSidedExitDownTime X (-x) ω then
          ENNReal.ofReal
            (Real.exp (-(q * ENNReal.toReal (twoSidedExitUpTime X (a - x) ω))))
        else 0) * ENNReal.ofReal (W a) ∂μ) := by
      apply lintegral_congr
      intro ω
      simpa only [ite_mul, zero_mul] using
        (chat04_strict_upper_exit_scale_payoff X W q a x hxa ω)
    _ = (∫⁻ ω,
        if twoSidedExitUpTime X (a - x) ω <
            twoSidedExitDownTime X (-x) ω then
          ENNReal.ofReal
            (Real.exp (-(q * ENNReal.toReal (twoSidedExitUpTime X (a - x) ω))))
        else 0 ∂μ) * ENNReal.ofReal (W a) := by
      rw [lintegral_mul_const _ hm]
