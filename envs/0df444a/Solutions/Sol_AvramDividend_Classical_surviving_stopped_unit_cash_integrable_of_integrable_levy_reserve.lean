-- Prove2me | solution 1 for AvramDividend.Classical.surviving_stopped_unit_cash_integrable_of_integrable_levy_reserve
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-10-24T22:30:55.994792+00:00
-- url     : https://prove2.me/submissions/0665efa9-6d4a-4e31-ac15-ae101b329bcf

import Mathlib.MeasureTheory.Function.L1Space.Integrable
import Mathlib.MeasureTheory.Integral.Lebesgue.Basic
import Mathlib.MeasureTheory.Constructions.BorelSpace.Order
import Mathlib.Data.ENNReal.Basic
import Theorems.Thm_AvramDividend_Classical_ruinTime_measurable
import Theorems.Thm_AvramDividend_Classical_stopped_discounted_unit_cash_measurable_of_strategy
import Theorems.Thm_AvramDividend_Classical_surviving_stopped_unit_cash_expected_finite_of_integrable_levy_reserve

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory Set Filter AvramDividend.Classical
open scoped NNReal ENNReal

/-- Integrable surviving cash follows from a finite extended first moment. -/
theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕) (x : ℝ)
    (D : ℝ≥0 → Ω → ℝ) (hD : IsDividendStrategy 𝓕 D)
    (q : ℝ) (hq : 0 ≤ q)
    (T S : ℝ≥0) (hTS : T < S)
    (hXI : Integrable (fun ω => x + X.X S ω) P)
    (k : ℕ) :
    Integrable (fun ω : Ω =>
      if (S : ℝ≥0∞) < ruinTime X x D ω then
        (∫⁻ r in
          (paymentTimes (ruinTime X x D ω) ∩ Iic (T : ℝ)) ∩
            Ico (k : ℝ) ((k : ℝ) + 1),
          ENNReal.ofReal (Real.exp (-(q * r))) ∂(dividendMeasure D ω)).toReal
      else 0) P := by
  have hτ : Measurable (ruinTime X x D) :=
    ruinTime_measurable X x D hD
  have hSurv : MeasurableSet
      {ω : Ω | (S : ℝ≥0∞) < ruinTime X x D ω} :=
    measurableSet_lt measurable_const hτ
  have hCashM :=
    stopped_discounted_unit_cash_measurable_of_strategy X q x D hD T k
  have hRealM : Measurable (fun ω : Ω =>
      if (S : ℝ≥0∞) < ruinTime X x D ω then
        (∫⁻ r in
          (paymentTimes (ruinTime X x D ω) ∩ Iic (T : ℝ)) ∩
            Ico (k : ℝ) ((k : ℝ) + 1),
          ENNReal.ofReal (Real.exp (-(q * r))) ∂(dividendMeasure D ω)).toReal
      else 0) :=
    Measurable.ite hSurv (ENNReal.measurable_toReal.comp hCashM) measurable_const
  have hNonneg : ∀ᵐ ω ∂P, 0 ≤
      (if (S : ℝ≥0∞) < ruinTime X x D ω then
        (∫⁻ r in
          (paymentTimes (ruinTime X x D ω) ∩ Iic (T : ℝ)) ∩
            Ico (k : ℝ) ((k : ℝ) + 1),
          ENNReal.ofReal (Real.exp (-(q * r))) ∂(dividendMeasure D ω)).toReal
        else 0) := by
    refine Filter.Eventually.of_forall ?_
    intro ω
    by_cases hs : (S : ℝ≥0∞) < ruinTime X x D ω
    · simpa only [if_pos hs] using
        (ENNReal.toReal_nonneg : 0 ≤
          (∫⁻ r in
            (paymentTimes (ruinTime X x D ω) ∩ Iic (T : ℝ)) ∩
              Ico (k : ℝ) ((k : ℝ) + 1),
            ENNReal.ofReal (Real.exp (-(q * r))) ∂(dividendMeasure D ω)).toReal)
    · simp [hs]
  have hExpected :=
    surviving_stopped_unit_cash_expected_finite_of_integrable_levy_reserve
      X x D hD q hq (ruinTime X x D) T S hTS hXI k
  have hFin : (∫⁻ ω, ENNReal.ofReal
      (if (S : ℝ≥0∞) < ruinTime X x D ω then
        (∫⁻ r in
          (paymentTimes (ruinTime X x D ω) ∩ Iic (T : ℝ)) ∩
            Ico (k : ℝ) ((k : ℝ) + 1),
          ENNReal.ofReal (Real.exp (-(q * r))) ∂(dividendMeasure D ω)).toReal
        else 0) ∂P) ≠ ⊤ := by
    apply ne_of_lt
    apply lt_of_le_of_lt ?_ (lt_top_iff_ne_top.mpr hExpected)
    apply lintegral_mono
    intro ω
    by_cases hs : (S : ℝ≥0∞) < ruinTime X x D ω
    · simp only [if_pos hs]
      exact ENNReal.ofReal_toReal_le
    · simp [hs]
  exact (lintegral_ofReal_ne_top_iff_integrable
    hRealM.aestronglyMeasurable hNonneg).mp hFin
