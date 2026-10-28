-- Prove2me | solution 1 for AvramDividend.Classical.stopped_unit_cash_integrable_of_stopped_payout_integrable
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-10-24T22:12:59.145087+00:00
-- url     : https://prove2.me/submissions/3556b7d6-ce3a-4024-98c3-0771ed32478a

import Mathlib.MeasureTheory.Function.L1Space.Integrable
import Mathlib.Data.ENNReal.Real
import Theorems.Thm_AvramDividend_Classical_discounted_stieltjes_lintegral_le_measure
import Theorems.Thm_AvramDividend_Classical_dividendMeasure_paymentWindow_finite_of_strategy
import Theorems.Thm_AvramDividend_Classical_paymentTimes_measurable
import Theorems.Thm_AvramDividend_Classical_stopped_discounted_unit_cash_measurable_of_strategy

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory Set AvramDividend.Classical
open scoped NNReal ENNReal

/-- Integrability of the stopped total Stieltjes payout dominates every unit cash block. -/
theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (q : ℝ) (hq : 0 ≤ q) (x : ℝ)
    (D : ℝ≥0 → Ω → ℝ) (hD : IsDividendStrategy 𝓕 D)
    (T : ℝ≥0)
    (hTotalI : Integrable (fun ω : Ω =>
      (∫⁻ t in paymentTimes (ruinTime X x D ω) ∩ Iic (T : ℝ),
        ENNReal.ofReal (Real.exp (-(q * t))) ∂(dividendMeasure D ω)).toReal) P)
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
  refine hTotalI.mono hMeas.aestronglyMeasurable ?_
  filter_upwards [] with ω
  let A : Set ℝ := paymentTimes (ruinTime X x D ω) ∩ Iic (T : ℝ)
  have hA : MeasurableSet A :=
    (paymentTimes_measurable (ruinTime X x D ω)).inter measurableSet_Iic
  have hAnonneg : ∀ t ∈ A, 0 ≤ t := by
    intro t ht
    exact ht.1.1
  have hDiscount :=
    discounted_stieltjes_lintegral_le_measure q hq
      (dividendMeasure D ω) A hA hAnonneg
  have hFinite : (dividendMeasure D ω) A < ⊤ :=
    lt_top_iff_ne_top.mpr
      (dividendMeasure_paymentWindow_finite_of_strategy D hD ω (ruinTime X x D ω) T)
  have hWhole : (∫⁻ t in A,
      ENNReal.ofReal (Real.exp (-(q * t))) ∂(dividendMeasure D ω)) ≠ ⊤ :=
    (lt_of_le_of_lt hDiscount hFinite).ne
  have hBlock :
      (∫⁻ t in A ∩ Ico (k : ℝ) ((k : ℝ) + 1),
        ENNReal.ofReal (Real.exp (-(q * t))) ∂(dividendMeasure D ω)) ≤
      (∫⁻ t in A,
        ENNReal.ofReal (Real.exp (-(q * t))) ∂(dividendMeasure D ω)) :=
    lintegral_mono_set Set.inter_subset_left
  have hBound := ENNReal.toReal_mono hWhole hBlock
  simpa only [A, Real.norm_eq_abs, abs_of_nonneg ENNReal.toReal_nonneg] using hBound