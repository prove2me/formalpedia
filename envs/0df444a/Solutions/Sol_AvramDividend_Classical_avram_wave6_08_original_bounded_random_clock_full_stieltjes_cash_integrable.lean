-- Prove2me | solution 1 for AvramDividend.Classical.avram_wave6_08_original_bounded_random_clock_full_stieltjes_cash_integrable
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-01T23:45:05.830995+00:00
-- url     : https://prove2.me/submissions/3801c804-2ef7-4094-bfa8-678b14280204

import Mathlib.MeasureTheory.Function.L1Space.Integrable
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_DividendStrategy
import Theorems.Thm_AvramDividend_Classical_avram_wave6_06_original_random_upper_clock_complete_stieltjes_cash_measurable
import Theorems.Thm_AvramDividend_Classical_avram_wave8_ubv_original_bounded_random_clock_expected_stieltjes_envelope

open MeasureTheory Set AvramDividend.Classical
open scoped NNReal ENNReal
set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕) (x : ℝ) (C : ℝ≥0∞)
    (D : ℝ≥0 → Ω → ℝ) (hD : IsAdmissibleLe X x C D)
    (q : ℝ) (τ : Ω → ℝ≥0) (T : ℝ≥0)
    (hτmeas : Measurable (fun ω => (τ ω : ℝ)))
    (hτBound : ∀ ω, τ ω ≤ T) :
    Integrable (fun ω =>
      (∫⁻ s in paymentTimes (ruinTime X x D ω) ∩ Iic (τ ω : ℝ),
        ENNReal.ofReal (Real.exp (-(q * s))) ∂(dividendMeasure D ω)).toReal) P := by
  let Cash : Ω → ℝ≥0∞ := fun ω =>
    ∫⁻ s in paymentTimes (ruinTime X x D ω) ∩ Iic (τ ω : ℝ),
      ENNReal.ofReal (Real.exp (-(q * s))) ∂(dividendMeasure D ω)
  have hmeas : Measurable Cash :=
    avram_wave6_06_original_random_upper_clock_complete_stieltjes_cash_measurable
      X x D hD.1.1 q (fun ω => (τ ω : ℝ)) hτmeas
  have hbound :
      (∫⁻ ω, Cash ω ∂P) ≤
        ENNReal.ofReal (Real.exp
          (|X.ψ 1 - q| * (((((T : ℝ).toNNReal + 1 : ℝ≥0) : ℝ))))) *
          ENNReal.ofReal (Real.exp x) :=
    avram_wave8_ubv_original_bounded_random_clock_expected_stieltjes_envelope
      X x C D hD q τ T hτBound
  have hfinite :
      ENNReal.ofReal (Real.exp
        (|X.ψ 1 - q| * (((((T : ℝ).toNNReal + 1 : ℝ≥0) : ℝ))))) *
        ENNReal.ofReal (Real.exp x) < ⊤ := by
    apply ENNReal.mul_lt_top
    · simp
    · simp
  have hcashfinite : (∫⁻ ω, Cash ω ∂P) ≠ ⊤ :=
    ne_of_lt (lt_of_le_of_lt hbound hfinite)
  exact integrable_toReal_of_lintegral_ne_top hmeas.aemeasurable hcashfinite
