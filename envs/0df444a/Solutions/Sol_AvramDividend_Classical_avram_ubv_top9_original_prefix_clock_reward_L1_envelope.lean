-- Prove2me | solution 1 for AvramDividend.Classical.avram_ubv_top9_original_prefix_clock_reward_L1_envelope
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-07T17:29:00.669345+00:00
-- url     : https://prove2.me/submissions/b3fe8e78-0cfc-42b2-b00e-7d7883457a3c

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_DividendStrategy
import Theorems.Thm_AvramDividend_Classical_avram_ubv_top9_original_prefix_rightpaid_reserve_upper
import Theorems.Thm_AvramDividend_Classical_avram_ubv_top9_source_topcap_discount_terminal_envelope
import Theorems.Thm_AvramDividend_Classical_avram_wave6_06_original_bounded_clock_stieltjes_cash_ae_finite
import Theorems.Thm_AvramDividend_Classical_avram_p4_e_localise_original_ruin_payment_cash_real_monotone_of_ae_finite
set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory Set AvramDividend.Classical
open scoped NNReal ENNReal
noncomputable section

/-- A common per-band L1 majorant for the exact post-rightpayment reward. -/
theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (w : ℝ → ℝ) (C : ℝ≥0∞) (hTop : C = ⊤)
    (hw0 : 0 ≤ w 0) (hw_cont : ContinuousOn w (Ici 0))
    (hw_neg : ∀ y : ℝ, y < 0 → w y = 0)
    (hw_smooth : ContDiffOn ℝ 2 w {y : ℝ | 0 < y ∧ ENNReal.ofReal y < C})
    (q : ℝ) (hq : 0 ≤ q)
    (hw_gen : ∀ y : ℝ, 0 < y → ENNReal.ofReal y < C →
      X.GeneratorIntegrable w y ∧ X.generator w y - q * w y ≤ 0)
    (hw_grad : ∀ y : ℝ, 0 < y → ENNReal.ofReal y < C →
      1 ≤ deriv w y)
    (x : ℝ) (D : ℝ≥0 → Ω → ℝ) (hD : IsAdmissibleLe X x C D)
    (τ ρ : Ω → ℝ≥0) (hρle : ∀ ω, ρ ω ≤ τ ω)
    (T : ℝ≥0) (hτBound : ∀ ω, τ ω ≤ T)
    (B : ℝ) (hB : 0 < x + B)
    (hXprefix : ∀ ω (t : ℝ≥0), t ≤ ρ ω → X.X t ω ≤ B) :
    ∀ᵐ ω ∂P,
      Real.exp (-(q * (ρ ω : ℝ))) *
        w (if ρ ω = 0 ∨ (ρ ω : ℝ≥0∞) < ruinTime X x D ω
          then x + X.X (ρ ω) ω - rightLimit D (ρ ω) ω
          else riskProcess X x D (ρ ω) ω) +
      (∫⁻ s in paymentTimes (ruinTime X x D ω) ∩ Iic (ρ ω : ℝ),
        ENNReal.ofReal (Real.exp (-(q * s))) ∂(dividendMeasure D ω)).toReal ≤
      w (x + B) +
      (∫⁻ s in paymentTimes (ruinTime X x D ω) ∩ Iic (τ ω : ℝ),
        ENNReal.ofReal (Real.exp (-(q * s))) ∂(dividendMeasure D ω)).toReal := by
  let V : Ω → ℝ := fun ω =>
    if ρ ω = 0 ∨ (ρ ω : ℝ≥0∞) < ruinTime X x D ω
    then x + X.X (ρ ω) ω - rightLimit D (ρ ω) ω
    else riskProcess X x D (ρ ω) ω
  have hV : ∀ ω, V ω ≤ x + B :=
    avram_ubv_top9_original_prefix_rightpaid_reserve_upper
      X x D hD.1.1 ρ B hXprefix
  have hTerminal : ∀ ω,
      Real.exp (-(q * (ρ ω : ℝ))) * w (V ω) ≤ w (x + B) := by
    intro ω
    exact (avram_ubv_top9_source_topcap_discount_terminal_envelope
      X w C hTop hw0 hw_cont hw_neg hw_smooth q hq hw_gen hw_grad
      (x + B) hB V hV ρ ω).2
  have hFinite :=
    avram_wave6_06_original_bounded_clock_stieltjes_cash_ae_finite
      X x C D hD q τ T hτBound
  have hCashLe :=
    avram_p4_e_localise_original_ruin_payment_cash_real_monotone_of_ae_finite
      X x D q ρ τ hρle hFinite
  filter_upwards [hCashLe] with ω hcash
  have hterm := hTerminal ω
  change Real.exp (-(q * (ρ ω : ℝ))) * w (V ω) +
    (∫⁻ s in paymentTimes (ruinTime X x D ω) ∩ Iic (ρ ω : ℝ),
      ENNReal.ofReal (Real.exp (-(q * s))) ∂(dividendMeasure D ω)).toReal ≤
    w (x + B) +
    (∫⁻ s in paymentTimes (ruinTime X x D ω) ∩ Iic (τ ω : ℝ),
      ENNReal.ofReal (Real.exp (-(q * s))) ∂(dividendMeasure D ω)).toReal
  linarith
