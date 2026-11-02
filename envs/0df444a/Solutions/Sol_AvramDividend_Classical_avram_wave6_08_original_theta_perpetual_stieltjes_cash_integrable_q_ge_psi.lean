-- Prove2me | solution 1 for AvramDividend.Classical.avram_wave6_08_original_theta_perpetual_stieltjes_cash_integrable_q_ge_psi
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-02T00:21:16.976182+00:00
-- url     : https://prove2.me/submissions/6b565eea-ef2e-419b-a2b6-2fbf060157ee

import Mathlib.MeasureTheory.Function.L1Space.Integrable
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_DividendStrategy
import Theorems.Thm_AvramDividend_Classical_avram_wave6_08_original_perpetual_stieltjes_cash_measurable
import Theorems.Thm_AvramDividend_Classical_avram_wave6_08_original_theta_perpetual_expected_cash_q_ge_psi
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
    (θ : ℝ) (hθ : 0 < θ) (q : ℝ) (hq : X.ψ θ ≤ q) :
    Integrable (fun ω =>
      (∫⁻ t in paymentTimes (ruinTime X x D ω),
        ENNReal.ofReal (Real.exp (-(q * t))) ∂dividendMeasure D ω).toReal) P := by
  let Cash : Ω → ℝ≥0∞ := fun ω =>
    ∫⁻ t in paymentTimes (ruinTime X x D ω),
      ENNReal.ofReal (Real.exp (-(q * t))) ∂dividendMeasure D ω
  have hMeas : Measurable Cash :=
    avram_wave6_08_original_perpetual_stieltjes_cash_measurable X x D hD.1.1 q
  have hBound : ENNReal.ofReal θ * (∫⁻ ω, Cash ω ∂P) ≤
      ENNReal.ofReal (Real.exp (θ * x)) :=
    avram_wave6_08_original_theta_perpetual_expected_cash_q_ge_psi
      X x C D hD θ hθ q hq
  have hθne : ENNReal.ofReal θ ≠ 0 :=
    ne_of_gt (ENNReal.ofReal_pos.mpr hθ)
  have hCashFinite : (∫⁻ ω, Cash ω ∂P) ≠ ⊤ := by
    intro htop
    have htopmul : ENNReal.ofReal θ * (⊤ : ℝ≥0∞) = ⊤ := by
      simp [hθne]
    rw [htop, htopmul] at hBound
    have hfinite : ENNReal.ofReal (Real.exp (θ * x)) < ⊤ := by simp
    exact (not_le_of_gt hfinite) hBound
  exact integrable_toReal_of_lintegral_ne_top hMeas.aemeasurable hCashFinite
