-- Prove2me | solution 1 for AvramDividend.Classical.avram_wave5_05_original_ae_stopped_complete_stieltjes_budget_to_full
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-01T19:45:54.788158+00:00
-- url     : https://prove2.me/submissions/0b5ca7ca-de7c-4280-b364-9048624bfddb

import Mathlib.Analysis.Complex.Exponential
import Mathlib.MeasureTheory.Integral.Lebesgue.Basic
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_DividendStrategy
import Theorems.Thm_AvramDividend_Classical_avram_wave5_05_original_ae_exhaustion_measurable_monotone_clock
import Theorems.Thm_AvramDividend_Classical_avram_wave4_04b_expected_preruin_complete_stieltjes_localisation
import Theorems.Thm_AvramDividend_Classical_ruinTime_stopping_rightCont_filtration
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
    (x : ℝ) (D : ℝ≥0 → Ω → ℝ)
    (hD : IsDividendStrategy 𝓕 D)
    (T : ℝ≥0) (q : ℝ)
    (S : ℕ → Ω → ℝ≥0∞)
    (hSm : ∀ n, Measurable (S n))
    (hTailAE : ∀ᵐ ω ∂P,
      (⨆ n, (⨅ m, if n ≤ m then S m ω else ⊤)) = ⊤)
    (B : ℝ≥0∞)
    (hBudget : ∀ n,
      (∫⁻ ω, ∫⁻ t in
          paymentTimes (min (ruinTime X x D ω) (S n ω)) ∩ Iic (T : ℝ),
        ENNReal.ofReal (Real.exp (-(q * t)))
          ∂dividendMeasure D ω ∂P) ≤ B) :
    (∫⁻ ω, ∫⁻ t in
        paymentTimes (ruinTime X x D ω) ∩ Iic (T : ℝ),
      ENNReal.ofReal (Real.exp (-(q * t)))
        ∂dividendMeasure D ω ∂P) ≤ B := by
  have hρ : Measurable (ruinTime X x D) := (ruinTime_stopping_rightCont_filtration X x D hD).measurable'
  obtain ⟨τ, hτmeas, hτmono, hτsup, hτle⟩ :=
    avram_wave5_05_original_ae_exhaustion_measurable_monotone_clock
      (ruinTime X x D) hρ S hSm hTailAE
  have hτbudget (n : ℕ) :
      (∫⁻ ω, ∫⁻ t in
          paymentTimes (τ n ω) ∩ Iic (T : ℝ),
        ENNReal.ofReal (Real.exp (-(q * t)))
          ∂dividendMeasure D ω ∂P) ≤ B := by
    calc
      (∫⁻ ω, ∫⁻ t in
          paymentTimes (τ n ω) ∩ Iic (T : ℝ),
        ENNReal.ofReal (Real.exp (-(q * t)))
          ∂dividendMeasure D ω ∂P) ≤
        (∫⁻ ω, ∫⁻ t in
          paymentTimes (min (ruinTime X x D ω) (S n ω)) ∩ Iic (T : ℝ),
        ENNReal.ofReal (Real.exp (-(q * t)))
          ∂dividendMeasure D ω ∂P) := by
            apply lintegral_mono_ae
            filter_upwards [hτle n] with ω hω
            have hr : τ n ω ≤ ruinTime X x D ω :=
              le_trans hω (min_le_left _ _)
            have hs : τ n ω ≤ S n ω :=
              le_trans hω (min_le_right _ _)
            apply lintegral_mono_set
            intro t ht
            have ht' :
                t ∈ paymentTimes
                  (min (ruinTime X x D ω) (τ n ω)) := by
              simpa [min_eq_right hr] using ht.1
            exact ⟨paymentTimes_min_mono_horizon
              (ruinTime X x D ω) (τ n ω) (S n ω)
              hs ht', ht.2⟩
      _ ≤ B := hBudget n
  have hLocEq :=
    avram_wave4_04b_expected_preruin_complete_stieltjes_localisation
      X x D hD T q τ hτmeas hτmono hτsup
  have hLocEq' :
      (∫⁻ ω, ∫⁻ t in
          paymentTimes (ruinTime X x D ω) ∩ Iic (T : ℝ),
        ENNReal.ofReal (Real.exp (-(q * t)))
          ∂dividendMeasure D ω ∂P) =
      ⨆ n, (∫⁻ ω, ∫⁻ t in
          paymentTimes (τ n ω) ∩ Iic (T : ℝ),
        ENNReal.ofReal (Real.exp (-(q * t)))
          ∂dividendMeasure D ω ∂P) := by
    simpa only [neg_mul] using hLocEq
  rw [hLocEq']
  exact iSup_le hτbudget
