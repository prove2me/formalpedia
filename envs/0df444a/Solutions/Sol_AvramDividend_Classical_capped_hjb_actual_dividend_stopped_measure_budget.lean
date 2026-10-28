-- Prove2me | solution 1 for AvramDividend.Classical.capped_hjb_actual_dividend_stopped_measure_budget
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-10-24T08:19:08.152986+00:00
-- url     : https://prove2.me/submissions/30575f08-b3ea-4554-b5d6-35e85df41a36

import Mathlib.MeasureTheory.Integral.Bochner.Basic
import Theorems.Thm_AvramDividend_Classical_capped_hjb_integrated_drift_dividend_residual_nonpos
import Theorems.Thm_AvramDividend_Classical_paymentTimes_measurable

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory Set
open scoped NNReal ENNReal
open AvramDividend.Classical

/-- The integrated HJB drift and singular marginal dividend residuals have a nonpositive sum when evaluated on a genuine dividend strategy's stopped payment set and its Stieltjes measure. The theorem specialises the proved abstract signed-budget result to the exact paymentTimes and dividendMeasure interface used by stochastic verification. -/
theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (D : ℝ≥0 → Ω → ℝ) (hD : IsDividendStrategy 𝓕 D)
    (q : ℝ) (w : ℝ → ℝ) (C : ℝ≥0∞)
    (hw_hjb : ∀ y : ℝ, 0 < y → ENNReal.ofReal y < C →
      X.GeneratorIntegrable w y ∧
        max (X.generator w y - q * w y) (1 - deriv w y) = 0)
    (σ : ℝ≥0∞) (T : ℝ≥0) (ω : Ω)
    (μtime : Measure ℝ) (u : ℝ → ℝ)
    (hregion : ∀ t ∈ paymentTimes σ ∩ Iic (T : ℝ),
      0 < u t ∧ ENNReal.ofReal (u t) < C)
    (hTime : IntegrableOn (fun t : ℝ =>
      Real.exp (-(q * t)) * (X.generator w (u t) - q * w (u t)))
      (paymentTimes σ ∩ Iic (T : ℝ)) μtime)
    (hDiv : IntegrableOn (fun t : ℝ =>
      Real.exp (-(q * t)) * (1 - deriv w (u t)))
      (paymentTimes σ ∩ Iic (T : ℝ)) (dividendMeasure D ω)) :
    (∫ t in paymentTimes σ ∩ Iic (T : ℝ),
      Real.exp (-(q * t)) *
        (X.generator w (u t) - q * w (u t)) ∂μtime) +
    (∫ t in paymentTimes σ ∩ Iic (T : ℝ),
      Real.exp (-(q * t)) *
        (1 - deriv w (u t)) ∂(dividendMeasure D ω)) ≤ 0 := by
  exact capped_hjb_integrated_drift_dividend_residual_nonpos
    X q w C hw_hjb μtime (dividendMeasure D ω)
    u (paymentTimes σ ∩ Iic (T : ℝ))
    ((paymentTimes_measurable σ).inter measurableSet_Iic)
    hregion hTime hDiv
