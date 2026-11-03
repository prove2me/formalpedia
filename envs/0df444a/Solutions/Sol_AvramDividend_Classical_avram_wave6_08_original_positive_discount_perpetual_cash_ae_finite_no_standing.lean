-- Prove2me | solution 1 for AvramDividend.Classical.avram_wave6_08_original_positive_discount_perpetual_cash_ae_finite_no_standing
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-02T07:27:27.206035+00:00
-- url     : https://prove2.me/submissions/8a530653-7002-4ae8-bb58-729e192b3e1d

import Mathlib.Analysis.Complex.Exponential
import Mathlib.MeasureTheory.Integral.Lebesgue.Markov
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_DividendStrategy
import Theorems.Thm_AvramDividend_Classical_avram_wave6_08_source_psi_positive_small_tilt_below_any_positive_discount
import Theorems.Thm_AvramDividend_Classical_avram_wave6_08_original_theta_perpetual_expected_cash_q_ge_psi
import Theorems.Thm_AvramDividend_Classical_avram_wave6_08_original_perpetual_stieltjes_cash_measurable
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
    (q : ℝ) (hq : 0 < q) :
    ∀ᵐ ω ∂P,
      (∫⁻ t in paymentTimes (ruinTime X x D ω),
        ENNReal.ofReal (Real.exp (-(q * t))) ∂dividendMeasure D ω) < ⊤ := by
  obtain ⟨θ, hθ, hψ⟩ :=
    avram_wave6_08_source_psi_positive_small_tilt_below_any_positive_discount X q hq
  let Cash : Ω → ℝ≥0∞ := fun ω =>
    ∫⁻ t in paymentTimes (ruinTime X x D ω),
      ENNReal.ofReal (Real.exp (-(q * t))) ∂dividendMeasure D ω
  have hMeas : Measurable Cash :=
    avram_wave6_08_original_perpetual_stieltjes_cash_measurable X x D hD.1.1 q
  have hBound : ENNReal.ofReal θ * (∫⁻ ω, Cash ω ∂P) ≤
      ENNReal.ofReal (Real.exp (θ * x)) :=
    avram_wave6_08_original_theta_perpetual_expected_cash_q_ge_psi
      X x C D hD θ hθ q (le_of_lt hψ)
  have hθne : ENNReal.ofReal θ ≠ 0 :=
    ne_of_gt (ENNReal.ofReal_pos.mpr hθ)
  have hCashFinite : (∫⁻ ω, Cash ω ∂P) ≠ ⊤ := by
    intro htop
    have htopmul : ENNReal.ofReal θ * (⊤ : ℝ≥0∞) = ⊤ := by
      simp [hθne]
    rw [htop, htopmul] at hBound
    have hfinite : ENNReal.ofReal (Real.exp (θ * x)) < ⊤ := by simp
    exact (not_le_of_gt hfinite) hBound
  exact MeasureTheory.ae_lt_top hMeas hCashFinite
