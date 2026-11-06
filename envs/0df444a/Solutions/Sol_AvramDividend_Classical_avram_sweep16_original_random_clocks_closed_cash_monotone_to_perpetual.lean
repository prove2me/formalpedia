-- Prove2me | solution 1 for AvramDividend.Classical.avram_sweep16_original_random_clocks_closed_cash_monotone_to_perpetual
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-05T12:08:01.974496+00:00
-- url     : https://prove2.me/submissions/2fb7a28e-1145-4437-9dc3-19a554b62787

import Mathlib.Probability.Process.Filtration
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_DividendStrategy

open MeasureTheory Set
open scoped NNReal ENNReal
open AvramDividend.Classical

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕) (q x : ℝ)
    (D : ℝ≥0 → Ω → ℝ) (τ σ : Ω → ℝ≥0)
    (hτσ : ∀ ω, τ ω ≤ σ ω) :
    (∫⁻ ω, ∫⁻ t in paymentTimes (ruinTime X x D ω) ∩ Iic (τ ω : ℝ),
      ENNReal.ofReal (Real.exp (-(q * t))) ∂(dividendMeasure D ω) ∂P) ≤
      (∫⁻ ω, ∫⁻ t in paymentTimes (ruinTime X x D ω) ∩ Iic (σ ω : ℝ),
        ENNReal.ofReal (Real.exp (-(q * t))) ∂(dividendMeasure D ω) ∂P) ∧
    (∫⁻ ω, ∫⁻ t in paymentTimes (ruinTime X x D ω) ∩ Iic (σ ω : ℝ),
      ENNReal.ofReal (Real.exp (-(q * t))) ∂(dividendMeasure D ω) ∂P) ≤
      dividendValue X q x D := by
  constructor
  · apply lintegral_mono
    intro ω
    apply lintegral_mono_set
    intro t ht
    have hclock : (τ ω : ℝ) ≤ (σ ω : ℝ) := by
      exact_mod_cast hτσ ω
    exact ⟨ht.1, le_trans ht.2 hclock⟩
  · unfold dividendValue
    apply lintegral_mono
    intro ω
    apply lintegral_mono_set
    intro t ht
    exact ht.1
