-- Prove2me | solution 1 for AvramDividend.Classical.stopped_unit_cash_integrable_of_cumulative_integrable
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-10-24T20:51:01.620525+00:00
-- url     : https://prove2.me/submissions/2547effb-b4c9-484e-90ca-a5b35fe5409b

import Mathlib.MeasureTheory.Function.L1Space.Integrable
import Mathlib.Data.ENNReal.Real
import Theorems.Thm_AvramDividend_Classical_discounted_dividend_window_le_cumulative
import Theorems.Thm_AvramDividend_Classical_stopped_discounted_unit_cash_measurable_of_strategy

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory Set AvramDividend.Classical
open scoped NNReal ENNReal

/-- An integrable cumulative-dividend bound makes each stopped exact
    unit-interval Stieltjes cash payment integrable in expectation. -/
theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (q : ℝ) (hq : 0 ≤ q) (x : ℝ)
    (D : ℝ≥0 → Ω → ℝ) (hD : IsDividendStrategy 𝓕 D)
    (T : ℝ≥0)
    (hDI : Integrable (fun ω : Ω =>
      (ENNReal.ofReal (D (T + 1) ω)).toReal) P)
    (k : ℕ) :
    Integrable (fun ω : Ω =>
      (∫⁻ t in
        (paymentTimes (ruinTime X x D ω) ∩ Iic (T : ℝ)) ∩
          Ico (k : ℝ) ((k : ℝ) + 1),
        ENNReal.ofReal (Real.exp (-(q * t))) ∂(dividendMeasure D ω)).toReal) P := by
  have hMeas : Measurable (fun ω : Ω =>
      (∫⁻ t in
        (paymentTimes (ruinTime X x D ω) ∩ Iic (T : ℝ)) ∩
          Ico (k : ℝ) ((k : ℝ) + 1),
        ENNReal.ofReal (Real.exp (-(q * t))) ∂(dividendMeasure D ω)).toReal) :=
    ENNReal.measurable_toReal.comp
      (stopped_discounted_unit_cash_measurable_of_strategy X q x D hD T k)
  refine hDI.mono hMeas.aestronglyMeasurable ?_
  filter_upwards [] with ω
  have hBlock :
      (∫⁻ t in
        (paymentTimes (ruinTime X x D ω) ∩ Iic (T : ℝ)) ∩
          Ico (k : ℝ) ((k : ℝ) + 1),
        ENNReal.ofReal (Real.exp (-(q * t))) ∂(dividendMeasure D ω)) ≤
      (∫⁻ t in paymentTimes (ruinTime X x D ω) ∩ Iic (T : ℝ),
        ENNReal.ofReal (Real.exp (-(q * t))) ∂(dividendMeasure D ω)) :=
    lintegral_mono_set Set.inter_subset_left
  have hCumulative :=
    discounted_dividend_window_le_cumulative D hD q hq
      (ruinTime X x D ω) T ω
  have hBound := ENNReal.toReal_mono
    (by simp : ENNReal.ofReal (D (T + 1) ω) ≠ ⊤)
    (hBlock.trans hCumulative)
  simpa only [Real.norm_eq_abs, abs_of_nonneg ENNReal.toReal_nonneg] using hBound
