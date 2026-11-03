-- Prove2me | solution 1 for AvramDividend.Classical.avram_wave7_11_original_expected_stieltjes_mono_random_clock
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-02T17:06:40.496284+00:00
-- url     : https://prove2.me/submissions/6b776aa0-f537-4b17-9ee7-65c649e987e6

import Definitions.Def_AvramDividend_Classical_DividendStrategy
import Mathlib.Analysis.Complex.Exponential
import Mathlib.MeasureTheory.Integral.Lebesgue.Basic

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory Set
open scoped NNReal ENNReal
open AvramDividend.Classical

/-- Expected original discounted Stieltjes dividends increase with a
    pointwise larger random payment stopping clock at the same real horizon. -/
theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    (D : ℝ≥0 → Ω → ℝ)
    (σ τ : Ω → ℝ≥0∞) (hστ : ∀ ω, σ ω ≤ τ ω)
    (q T : ℝ) :
    (∫⁻ ω, ∫⁻ t in paymentTimes (σ ω) ∩ Iic T,
      ENNReal.ofReal (Real.exp (-(q * t))) ∂(dividendMeasure D ω) ∂P) ≤
    (∫⁻ ω, ∫⁻ t in paymentTimes (τ ω) ∩ Iic T,
      ENNReal.ofReal (Real.exp (-(q * t))) ∂(dividendMeasure D ω) ∂P) := by
  apply lintegral_mono
  intro ω
  apply MeasureTheory.lintegral_mono_set
  intro t ht
  have hpay : t ∈ paymentTimes (σ ω) := ht.1
  have ht0 : 0 ≤ t := hpay.1
  have hcase : t = 0 ∨ ENNReal.ofReal t < σ ω := hpay.2
  refine ⟨?_, ht.2⟩
  change 0 ≤ t ∧ (t = 0 ∨ ENNReal.ofReal t < τ ω)
  refine ⟨ht0, ?_⟩
  rcases hcase with hz | hlt
  · exact Or.inl hz
  · exact Or.inr (lt_of_lt_of_le hlt (hστ ω))
