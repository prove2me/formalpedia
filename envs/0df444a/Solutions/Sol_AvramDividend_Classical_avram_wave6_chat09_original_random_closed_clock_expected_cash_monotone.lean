-- Prove2me | solution 1 for AvramDividend.Classical.avram_wave6_chat09_original_random_closed_clock_expected_cash_monotone
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-02T10:53:01.514128+00:00
-- url     : https://prove2.me/submissions/6da065e5-0b86-4fdc-af16-be50a5695864

import Mathlib.Analysis.Complex.Exponential
import Mathlib.MeasureTheory.MeasurableSpace.Defs
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_DividendStrategy

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory Set
open scoped NNReal ENNReal
open AvramDividend.Classical
noncomputable section

theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (x : ℝ) (D : ℝ≥0 → Ω → ℝ) (q : ℝ)
    (τ σ : Ω → ℝ≥0) (hτσ : ∀ ω, τ ω ≤ σ ω) :
    (∫⁻ ω, ∫⁻ t in
      paymentTimes (ruinTime X x D ω) ∩ Iic (τ ω : ℝ),
      ENNReal.ofReal (Real.exp (-(q * t))) ∂(dividendMeasure D ω) ∂P) ≤
    (∫⁻ ω, ∫⁻ t in
      paymentTimes (ruinTime X x D ω) ∩ Iic (σ ω : ℝ),
      ENNReal.ofReal (Real.exp (-(q * t))) ∂(dividendMeasure D ω) ∂P) := by
  have hTime (ω : Ω) : (τ ω : ℝ) ≤ (σ ω : ℝ) := by
    exact_mod_cast hτσ ω
  have hsub (ω : Ω) :
      paymentTimes (ruinTime X x D ω) ∩ Iic (τ ω : ℝ) ⊆
        paymentTimes (ruinTime X x D ω) ∩ Iic (σ ω : ℝ) := by
    intro t ht
    exact ⟨ht.1, le_trans ht.2 (hTime ω)⟩
  have hpath (ω : Ω) :
      (∫⁻ t in paymentTimes (ruinTime X x D ω) ∩ Iic (τ ω : ℝ),
        ENNReal.ofReal (Real.exp (-(q * t))) ∂(dividendMeasure D ω)) ≤
      (∫⁻ t in paymentTimes (ruinTime X x D ω) ∩ Iic (σ ω : ℝ),
        ENNReal.ofReal (Real.exp (-(q * t))) ∂(dividendMeasure D ω)) :=
    lintegral_mono_set (hsub ω)
  exact lintegral_mono hpath
