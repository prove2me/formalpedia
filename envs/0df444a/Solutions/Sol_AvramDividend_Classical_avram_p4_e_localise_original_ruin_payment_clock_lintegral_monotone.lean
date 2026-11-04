-- Prove2me | solution 1 for AvramDividend.Classical.avram_p4_e_localise_original_ruin_payment_clock_lintegral_monotone
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-03T15:07:03.726193+00:00
-- url     : https://prove2.me/submissions/586cc160-23e8-44a1-9458-0d9eda81c7b7

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
/-- Extending the original stopped clock preserves every allowed dividend atom and increases ENNReal cash. -/
theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕) (x : ℝ)
    (D : ℝ≥0 → Ω → ℝ) (q : ℝ)
    (τ σ : Ω → ℝ≥0) (hclock : ∀ ω, τ ω ≤ σ ω) :
    ∀ ω,
      (∫⁻ t in paymentTimes (ruinTime X x D ω) ∩ Iic (τ ω : ℝ),
        ENNReal.ofReal (Real.exp (-(q * t))) ∂(dividendMeasure D ω)) ≤
      (∫⁻ t in paymentTimes (ruinTime X x D ω) ∩ Iic (σ ω : ℝ),
        ENNReal.ofReal (Real.exp (-(q * t))) ∂(dividendMeasure D ω)) := by
  intro ω
  have hreal : (τ ω : ℝ) ≤ (σ ω : ℝ) := by
    exact_mod_cast hclock ω
  apply lintegral_mono_set
  intro t ht
  exact ⟨ht.1, le_trans ht.2 hreal⟩
