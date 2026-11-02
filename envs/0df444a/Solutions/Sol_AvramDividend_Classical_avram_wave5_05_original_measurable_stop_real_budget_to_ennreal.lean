-- Prove2me | solution 1 for AvramDividend.Classical.avram_wave5_05_original_measurable_stop_real_budget_to_ennreal
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-01T19:40:51.284449+00:00
-- url     : https://prove2.me/submissions/b5d81f7b-0eef-4953-9b36-90b731fdcb08

import Mathlib.Analysis.Complex.Exponential
import Mathlib.MeasureTheory.Integral.Lebesgue.Basic
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_DividendStrategy
import Theorems.Thm_AvramDividend_Classical_avram_wave5_05_original_measurable_stopping_clock_complete_stieltjes_real_ennreal_expectation_eq
import Theorems.Thm_AvramDividend_Classical_paymentTimes_min_mono_horizon

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory Set
open scoped NNReal ENNReal
open AvramDividend.Classical

theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (x : ℝ) (C : ℝ≥0∞)
    (D : ℝ≥0 → Ω → ℝ) (hD : IsAdmissibleLe X x C D)
    (T : ℝ) (hT : 0 ≤ T) (q : ℝ)
    (S : Ω → ℝ≥0∞) (hSm : Measurable S)
    (hCashFinite :
      (∫⁻ ω, ∫⁻ t in
          paymentTimes (ruinTime X x D ω) ∩ Iic T,
        ENNReal.ofReal (Real.exp (-(q * t)))
          ∂dividendMeasure D ω ∂P) < ⊤)
    (B : ℝ)
    (hRealBudget :
      (∫ ω,
        (∫⁻ t in
          paymentTimes (min (ruinTime X x D ω) (S ω)) ∩ Iic T,
          ENNReal.ofReal (Real.exp (-(q * t)))
            ∂dividendMeasure D ω).toReal ∂P) ≤ B) :
    (∫⁻ ω, ∫⁻ t in
        paymentTimes (min (ruinTime X x D ω) (S ω)) ∩ Iic T,
      ENNReal.ofReal (Real.exp (-(q * t)))
        ∂dividendMeasure D ω ∂P) ≤ ENNReal.ofReal B := by
  have hUpper :
      (∫⁻ ω, ∫⁻ t in
          paymentTimes (min (ruinTime X x D ω) (S ω)) ∩ Iic T,
        ENNReal.ofReal (Real.exp (-(q * t)))
          ∂dividendMeasure D ω ∂P) ≤
      (∫⁻ ω, ∫⁻ t in
          paymentTimes (ruinTime X x D ω) ∩ Iic T,
        ENNReal.ofReal (Real.exp (-(q * t)))
          ∂dividendMeasure D ω ∂P) := by
    apply lintegral_mono
    intro ω
    apply lintegral_mono_set
    intro t ht
    have hPay : t ∈ paymentTimes (ruinTime X x D ω) := by
      simpa using
        (paymentTimes_min_mono_horizon
          (ruinTime X x D ω) (S ω) ⊤ le_top ht.1)
    exact ⟨hPay, ht.2⟩
  have hNotTop :
      (∫⁻ ω, ∫⁻ t in
          paymentTimes (min (ruinTime X x D ω) (S ω)) ∩ Iic T,
        ENNReal.ofReal (Real.exp (-(q * t)))
          ∂dividendMeasure D ω ∂P) ≠ ⊤ :=
    ne_of_lt (lt_of_le_of_lt hUpper hCashFinite)
  have hReal :
      (∫⁻ ω, ∫⁻ t in
          paymentTimes (min (ruinTime X x D ω) (S ω)) ∩ Iic T,
        ENNReal.ofReal (Real.exp (-(q * t)))
          ∂dividendMeasure D ω ∂P).toReal ≤ B := by
    rw [← avram_wave5_05_original_measurable_stopping_clock_complete_stieltjes_real_ennreal_expectation_eq
      X x C D hD T hT q S hSm]
    exact hRealBudget
  calc
    (∫⁻ ω, ∫⁻ t in
        paymentTimes (min (ruinTime X x D ω) (S ω)) ∩ Iic T,
      ENNReal.ofReal (Real.exp (-(q * t)))
        ∂dividendMeasure D ω ∂P) =
      ENNReal.ofReal
        ((∫⁻ ω, ∫⁻ t in
            paymentTimes (min (ruinTime X x D ω) (S ω)) ∩ Iic T,
          ENNReal.ofReal (Real.exp (-(q * t)))
            ∂dividendMeasure D ω ∂P).toReal) :=
          (ENNReal.ofReal_toReal hNotTop).symm
    _ ≤ ENNReal.ofReal B :=
      ENNReal.ofReal_le_ofReal hReal
