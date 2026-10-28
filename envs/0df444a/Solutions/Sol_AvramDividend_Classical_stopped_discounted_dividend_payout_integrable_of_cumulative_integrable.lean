-- Prove2me | solution 1 for AvramDividend.Classical.stopped_discounted_dividend_payout_integrable_of_cumulative_integrable
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-10-24T20:58:55.379311+00:00
-- url     : https://prove2.me/submissions/027038b8-bd35-4d96-a835-c1cd4fd1f996

import Mathlib.MeasureTheory.Function.L1Space.Integrable
import Mathlib.Data.ENNReal.Real
import Theorems.Thm_AvramDividend_Classical_discounted_dividend_window_le_cumulative
import Theorems.Thm_AvramDividend_Classical_stopped_discounted_dividend_payout_measurable_of_strategy

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory Set AvramDividend.Classical
open scoped NNReal ENNReal

/-- Integrable cumulative dividends dominate the entire discounted stopped
    Stieltjes payout, including continuous and jump dividend payments. -/
theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (q : ℝ) (hq : 0 ≤ q) (x : ℝ)
    (D : ℝ≥0 → Ω → ℝ) (hD : IsDividendStrategy 𝓕 D)
    (T : ℝ≥0)
    (hDI : Integrable (fun ω : Ω =>
      (ENNReal.ofReal (D (T + 1) ω)).toReal) P) :
    Integrable (fun ω : Ω =>
      (∫⁻ t in paymentTimes (ruinTime X x D ω) ∩ Iic (T : ℝ),
        ENNReal.ofReal (Real.exp (-(q * t))) ∂(dividendMeasure D ω)).toReal) P := by
  have hMeas : Measurable (fun ω : Ω =>
      (∫⁻ t in paymentTimes (ruinTime X x D ω) ∩ Iic (T : ℝ),
        ENNReal.ofReal (Real.exp (-(q * t))) ∂(dividendMeasure D ω)).toReal) :=
    ENNReal.measurable_toReal.comp
      (stopped_discounted_dividend_payout_measurable_of_strategy
        X q hq x D hD T)
  refine hDI.mono hMeas.aestronglyMeasurable ?_
  filter_upwards [] with ω
  have hBound := ENNReal.toReal_mono
    (by simp : ENNReal.ofReal (D (T + 1) ω) ≠ ⊤)
    (discounted_dividend_window_le_cumulative D hD q hq
      (ruinTime X x D ω) T ω)
  simpa only [Real.norm_eq_abs, abs_of_nonneg ENNReal.toReal_nonneg] using hBound
