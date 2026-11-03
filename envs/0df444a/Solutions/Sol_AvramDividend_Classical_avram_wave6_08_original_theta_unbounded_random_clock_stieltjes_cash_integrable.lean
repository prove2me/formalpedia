-- Prove2me | solution 1 for AvramDividend.Classical.avram_wave6_08_original_theta_unbounded_random_clock_stieltjes_cash_integrable
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-02T06:42:02.677602+00:00
-- url     : https://prove2.me/submissions/3aa70999-f85b-4e1b-b665-7b28b1af4877

import Mathlib.MeasureTheory.Function.L1Space.Integrable
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_DividendStrategy
import Theorems.Thm_AvramDividend_Classical_avram_wave6_06_original_random_upper_clock_complete_stieltjes_cash_measurable
import Theorems.Thm_AvramDividend_Classical_avram_wave6_08_original_theta_unbounded_random_clock_stieltjes_budget
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
    (θ : ℝ) (hθ : 0 < θ) (q : ℝ) (hq : X.ψ θ ≤ q)
    (τ : Ω → ℝ≥0)
    (hτmeas : Measurable (fun ω => (τ ω : ℝ))) :
    Integrable (fun ω =>
      (∫⁻ t in paymentTimes (ruinTime X x D ω) ∩ Iic (τ ω : ℝ),
        ENNReal.ofReal (Real.exp (-(q * t))) ∂dividendMeasure D ω).toReal) P := by
  let Cash : Ω → ℝ≥0∞ := fun ω =>
    ∫⁻ t in paymentTimes (ruinTime X x D ω) ∩ Iic (τ ω : ℝ),
      ENNReal.ofReal (Real.exp (-(q * t))) ∂dividendMeasure D ω
  have hMeas : Measurable Cash := by
    have h := avram_wave6_06_original_random_upper_clock_complete_stieltjes_cash_measurable
      X x D hD.1.1 q (fun ω => (τ ω : ℝ)) hτmeas
    simpa only [Cash] using h
  have hBound : ENNReal.ofReal θ * (∫⁻ ω, Cash ω ∂P) ≤
      ENNReal.ofReal (Real.exp (θ * x)) :=
    avram_wave6_08_original_theta_unbounded_random_clock_stieltjes_budget
      X x C D hD θ hθ q hq τ hτmeas
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
