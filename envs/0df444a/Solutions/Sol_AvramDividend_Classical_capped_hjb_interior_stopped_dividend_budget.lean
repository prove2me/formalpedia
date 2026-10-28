-- Prove2me | solution 1 for AvramDividend.Classical.capped_hjb_interior_stopped_dividend_budget
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-10-24T10:18:02.378549+00:00
-- url     : https://prove2.me/submissions/d99d4b24-0166-4717-9bb4-20cb87f6df6e

import Mathlib.MeasureTheory.Integral.Bochner.Basic
import Theorems.Thm_AvramDividend_Classical_capped_hjb_integrated_drift_dividend_residual_nonpos
import Theorems.Thm_AvramDividend_Classical_paymentTimes_measurable

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory Set
open scoped NNReal ENNReal
open AvramDividend.Classical

/-- Localise the genuine stopped dividend Stieltjes measure and the time measure to the positive reserve interior below the cap. The region condition required by the general HJB signed-budget theorem follows directly from membership in the localisation set. This isolates the boundary and zero-reserve times which a stochastic stopped change-of-variables proof must treat separately. -/
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
    (hInterior : MeasurableSet
      {t : ℝ | 0 < u t ∧ ENNReal.ofReal (u t) < C})
    (hTime : IntegrableOn (fun t : ℝ =>
      Real.exp (-(q * t)) * (X.generator w (u t) - q * w (u t)))
      ((paymentTimes σ ∩ Iic (T : ℝ)) ∩
      {t : ℝ | 0 < u t ∧ ENNReal.ofReal (u t) < C}) μtime)
    (hDiv : IntegrableOn (fun t : ℝ =>
      Real.exp (-(q * t)) * (1 - deriv w (u t)))
      ((paymentTimes σ ∩ Iic (T : ℝ)) ∩
      {t : ℝ | 0 < u t ∧ ENNReal.ofReal (u t) < C}) (dividendMeasure D ω)) :
    (∫ t in (paymentTimes σ ∩ Iic (T : ℝ)) ∩
      {t : ℝ | 0 < u t ∧ ENNReal.ofReal (u t) < C},
      Real.exp (-(q * t)) *
        (X.generator w (u t) - q * w (u t)) ∂μtime) +
    (∫ t in (paymentTimes σ ∩ Iic (T : ℝ)) ∩
      {t : ℝ | 0 < u t ∧ ENNReal.ofReal (u t) < C},
      Real.exp (-(q * t)) *
        (1 - deriv w (u t)) ∂(dividendMeasure D ω)) ≤ 0 := by
  let A : Set ℝ := (paymentTimes σ ∩ Iic (T : ℝ)) ∩
      {t : ℝ | 0 < u t ∧ ENNReal.ofReal (u t) < C}
  have hAmeas : MeasurableSet A := by
    exact ((paymentTimes_measurable σ).inter measurableSet_Iic).inter hInterior
  have hregion : ∀ t ∈ A, 0 < u t ∧ ENNReal.ofReal (u t) < C := by
    intro t ht
    exact ht.2
  exact capped_hjb_integrated_drift_dividend_residual_nonpos
    X q w C hw_hjb μtime (dividendMeasure D ω)
    u A hAmeas hregion hTime hDiv
