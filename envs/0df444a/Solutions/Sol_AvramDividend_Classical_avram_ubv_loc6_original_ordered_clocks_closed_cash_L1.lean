-- Prove2me | solution 1 for AvramDividend.Classical.avram_ubv_loc6_original_ordered_clocks_closed_cash_L1
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-06T09:01:10.750518+00:00
-- url     : https://prove2.me/submissions/a359a44b-5a37-4c05-96c4-fd637bfd2d21

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_DividendStrategy
import Theorems.Thm_AvramDividend_Classical_avram_wave6_06_original_random_upper_clock_complete_stieltjes_cash_measurable
import Theorems.Thm_AvramDividend_Classical_avram_p4_d_dividend_original_literal_stopped_payment_cash_lintegral_finite

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory Set Filter Topology AvramDividend.Classical
open scoped NNReal ENNReal
noncomputable section

/-- A spatially clipped closed Stieltjes cash payoff is L1 whenever
    the exact original later natural-clock cash is L1. -/
theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕) (x q : ℝ) (hq : 0 ≤ q)
    (C : ℝ≥0∞) (D : ℝ≥0 → Ω → ℝ) (hD : IsAdmissibleLe X x C D)
    (σ τ : Ω → ℝ≥0) (hστ : ∀ ω, σ ω ≤ τ ω)
    (hσmeas : Measurable (fun ω => (σ ω : ℝ)))
    (hCashτI : Integrable (fun ω => (∫⁻ s in paymentTimes (ruinTime X x D ω) ∩ Iic (τ ω : ℝ),
      ENNReal.ofReal (Real.exp (-(q * s))) ∂(dividendMeasure D ω)).toReal) P) :
    Integrable (fun ω => (∫⁻ s in paymentTimes (ruinTime X x D ω) ∩ Iic (σ ω : ℝ),
      ENNReal.ofReal (Real.exp (-(q * s))) ∂(dividendMeasure D ω)).toReal) P := by
  have hMeasENN : Measurable (fun ω =>
      ∫⁻ s in paymentTimes (ruinTime X x D ω) ∩ Iic (σ ω : ℝ),
        ENNReal.ofReal (Real.exp (-(q * s))) ∂(dividendMeasure D ω)) :=
    avram_wave6_06_original_random_upper_clock_complete_stieltjes_cash_measurable
      X x D hD.1.1 q (fun ω => (σ ω : ℝ)) hσmeas
  have hMeas : AEStronglyMeasurable (fun ω => (∫⁻ s in paymentTimes (ruinTime X x D ω) ∩ Iic (σ ω : ℝ),
      ENNReal.ofReal (Real.exp (-(q * s))) ∂(dividendMeasure D ω)).toReal) P :=
    (ENNReal.measurable_toReal.comp hMeasENN).aestronglyMeasurable
  have hNN : ∀ᵐ ω ∂P, 0 ≤ (∫⁻ s in paymentTimes (ruinTime X x D ω) ∩ Iic (σ ω : ℝ),
      ENNReal.ofReal (Real.exp (-(q * s))) ∂(dividendMeasure D ω)).toReal := by
    filter_upwards [] with ω
    exact ENNReal.toReal_nonneg
  have hUpper : ∀ᵐ ω ∂P, (∫⁻ s in paymentTimes (ruinTime X x D ω) ∩ Iic (σ ω : ℝ),
      ENNReal.ofReal (Real.exp (-(q * s))) ∂(dividendMeasure D ω)).toReal ≤ (∫⁻ s in paymentTimes (ruinTime X x D ω) ∩ Iic (τ ω : ℝ),
      ENNReal.ofReal (Real.exp (-(q * s))) ∂(dividendMeasure D ω)).toReal := by
    filter_upwards [] with ω
    have hclock : (σ ω : ℝ) ≤ (τ ω : ℝ) := by
      exact_mod_cast hστ ω
    have hle : (∫⁻ s in paymentTimes (ruinTime X x D ω) ∩ Iic (σ ω : ℝ),
        ENNReal.ofReal (Real.exp (-(q * s))) ∂(dividendMeasure D ω)) ≤
        (∫⁻ s in paymentTimes (ruinTime X x D ω) ∩ Iic (τ ω : ℝ),
        ENNReal.ofReal (Real.exp (-(q * s))) ∂(dividendMeasure D ω)) := by
      apply lintegral_mono_set
      intro t ht
      exact ⟨ht.1, le_trans ht.2 hclock⟩
    have hfinite :=
      avram_p4_d_dividend_original_literal_stopped_payment_cash_lintegral_finite
        D hD.1.1 ω (ruinTime X x D ω) (τ ω) q hq
    exact ENNReal.toReal_mono (ne_of_lt hfinite) hle
  exact hCashτI.mono_nonneg hMeas hNN hUpper
