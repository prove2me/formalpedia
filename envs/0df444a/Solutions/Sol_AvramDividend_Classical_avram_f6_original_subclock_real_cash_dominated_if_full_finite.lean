-- Prove2me | solution 1 for AvramDividend.Classical.avram_f6_original_subclock_real_cash_dominated_if_full_finite
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-19T10:11:22.824417+00:00
-- url     : https://prove2.me/submissions/1254be7c-57de-4bdd-bd7e-6d85dfc49171

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_DividendStrategy
import Theorems.Thm_AvramDividend_Classical_avram_p4_e_localise_original_ruin_payment_clock_lintegral_monotone
set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

set_option autoImplicit false
open MeasureTheory Set Filter AvramDividend.Classical
open scoped NNReal ENNReal
noncomputable section

theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (x q : ℝ) (D : ℝ≥0 → Ω → ℝ)
    (τ : Ω → ℝ≥0) (σ : ℕ → Ω → ℝ≥0)
    (hclock : ∀ k ω, σ k ω ≤ τ ω)
    (hFullFinite : ∀ ω : Ω,
      (∫⁻ s in paymentTimes (ruinTime X x D ω) ∩ Iic (τ ω : ℝ),
        ENNReal.ofReal (Real.exp (-(q * s)))
        ∂(dividendMeasure D ω)) ≠ ⊤) :
    ∀ k ω,
      (∫⁻ s in paymentTimes (ruinTime X x D ω) ∩ Iic (σ k ω : ℝ),
        ENNReal.ofReal (Real.exp (-(q * s)))
        ∂(dividendMeasure D ω)).toReal ≤
      (∫⁻ s in paymentTimes (ruinTime X x D ω) ∩ Iic (τ ω : ℝ),
        ENNReal.ofReal (Real.exp (-(q * s)))
        ∂(dividendMeasure D ω)).toReal := by
  intro k ω
  have hMass :=
    avram_p4_e_localise_original_ruin_payment_clock_lintegral_monotone
      X x D q (σ k) τ (fun η => hclock k η) ω
  exact ENNReal.toReal_mono (hFullFinite ω) hMass
