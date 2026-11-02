-- Prove2me | solution 1 for AvramDividend.Classical.avram_wave5_05_original_measurable_stopping_clock_complete_stieltjes_real_ennreal_expectation_eq
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-01T19:24:36.322614+00:00
-- url     : https://prove2.me/submissions/68f79ec8-3a5f-4425-afc7-be78a1e3e415

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_DividendStrategy
import Theorems.Thm_AvramDividend_Classical_avram_wave5_05_original_arbitrary_measurable_stop_complete_stieltjes_reward_measurable
import Theorems.Thm_AvramDividend_Classical_avram_wave5_03_original_real_horizon_stopped_full_stieltjes_payment_ae_finite
import Theorems.Thm_AvramDividend_Classical_paymentTimes_min_mono_horizon

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory Set ProbabilityTheory
open scoped NNReal ENNReal
open AvramDividend.Classical

theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (x : ℝ) (C : ℝ≥0∞) (D : ℝ≥0 → Ω → ℝ)
    (hD : IsAdmissibleLe X x C D)
    (T : ℝ) (hT : 0 ≤ T) (q : ℝ)
    (S : Ω → ℝ≥0∞) (hSm : Measurable S) :
    (∫ ω,
      (∫⁻ t in
          paymentTimes (min (ruinTime X x D ω) (S ω)) ∩ Iic T,
        ENNReal.ofReal (Real.exp (-(q * t)))
          ∂dividendMeasure D ω).toReal ∂P) =
    (∫⁻ ω, ∫⁻ t in
        paymentTimes (min (ruinTime X x D ω) (S ω)) ∩ Iic T,
      ENNReal.ofReal (Real.exp (-(q * t)))
        ∂dividendMeasure D ω ∂P).toReal := by
  have hDiv : IsDividendStrategy 𝓕 D := by
    first
    | exact hD.1
    | exact hD.1.1
    | exact hD.1.1.1
  have hMeas :=
    avram_wave5_05_original_arbitrary_measurable_stop_complete_stieltjes_reward_measurable
      X x D hDiv q T S hSm
  have hFullCashAeFinite :
      ∀ᵐ ω ∂P,
        (∫⁻ t in paymentTimes (ruinTime X x D ω) ∩ Iic T,
          ENNReal.ofReal (Real.exp (-(q * t)))
            ∂dividendMeasure D ω) < ⊤ :=
    avram_wave5_03_original_real_horizon_stopped_full_stieltjes_payment_ae_finite
      X x C D hD T hT q
  have hStoppedCashAeFinite :
      ∀ᵐ ω ∂P,
        (∫⁻ t in
            paymentTimes (min (ruinTime X x D ω) (S ω)) ∩ Iic T,
          ENNReal.ofReal (Real.exp (-(q * t)))
            ∂dividendMeasure D ω) < ⊤ := by
    filter_upwards [hFullCashAeFinite] with ω hω
    apply lt_of_le_of_lt _ hω
    apply lintegral_mono_set
    intro t ht
    have hPay : t ∈ paymentTimes (ruinTime X x D ω) := by
      simpa using
        (paymentTimes_min_mono_horizon
          (ruinTime X x D ω) (S ω) ⊤ le_top ht.1)
    exact ⟨hPay, ht.2⟩
  exact integral_toReal hMeas.aemeasurable hStoppedCashAeFinite
