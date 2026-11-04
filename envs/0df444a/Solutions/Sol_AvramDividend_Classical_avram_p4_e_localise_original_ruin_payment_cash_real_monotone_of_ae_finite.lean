-- Prove2me | solution 1 for AvramDividend.Classical.avram_p4_e_localise_original_ruin_payment_cash_real_monotone_of_ae_finite
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-03T15:12:00.002708+00:00
-- url     : https://prove2.me/submissions/40251952-6610-427c-bf15-e49f9f3728c7

import Mathlib.Analysis.Complex.Exponential
import Mathlib.MeasureTheory.Integral.Lebesgue.Basic
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_DividendStrategy
set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory Set AvramDividend.Classical
open scoped NNReal ENNReal
noncomputable section
/-- Real-valued original cash is monotone when the larger exact Stieltjes lintegral is finite a.e. -/
theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕) (x : ℝ)
    (D : ℝ≥0 → Ω → ℝ) (q : ℝ)
    (τ σ : Ω → ℝ≥0) (hclock : ∀ ω, τ ω ≤ σ ω)
    (hfinite : ∀ᵐ ω ∂P,
      (∫⁻ t in paymentTimes (ruinTime X x D ω) ∩ Iic (σ ω : ℝ),
        ENNReal.ofReal (Real.exp (-(q * t))) ∂(dividendMeasure D ω)) < ⊤) :
    ∀ᵐ ω ∂P,
      (∫⁻ t in paymentTimes (ruinTime X x D ω) ∩ Iic (τ ω : ℝ),
        ENNReal.ofReal (Real.exp (-(q * t))) ∂(dividendMeasure D ω)).toReal ≤
      (∫⁻ t in paymentTimes (ruinTime X x D ω) ∩ Iic (σ ω : ℝ),
        ENNReal.ofReal (Real.exp (-(q * t))) ∂(dividendMeasure D ω)).toReal := by
  filter_upwards [hfinite] with ω hfin
  have hreal : (τ ω : ℝ) ≤ (σ ω : ℝ) := by
    exact_mod_cast hclock ω
  have hENN :
      (∫⁻ t in paymentTimes (ruinTime X x D ω) ∩ Iic (τ ω : ℝ),
        ENNReal.ofReal (Real.exp (-(q * t))) ∂(dividendMeasure D ω)) ≤
      (∫⁻ t in paymentTimes (ruinTime X x D ω) ∩ Iic (σ ω : ℝ),
        ENNReal.ofReal (Real.exp (-(q * t))) ∂(dividendMeasure D ω)) := by
    apply lintegral_mono_set
    intro t ht
    exact ⟨ht.1, le_trans ht.2 hreal⟩
  exact ENNReal.toReal_mono (ne_of_lt hfin) hENN
