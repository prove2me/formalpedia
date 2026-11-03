-- Prove2me | solution 1 for AvramDividend.Classical.avram_wave7_03_original_dividendValue_antitone_discount
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-02T20:10:32.692992+00:00
-- url     : https://prove2.me/submissions/e5a1ec8c-cf7c-4554-a6e1-8e18182c37bb

import Mathlib.MeasureTheory.Integral.Lebesgue.Basic
import Mathlib.Analysis.Complex.Exponential
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_DividendStrategy
import Theorems.Thm_AvramDividend_Classical_paymentTimes_measurable

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory Set
open scoped NNReal ENNReal
open AvramDividend.Classical
noncomputable section

/-- The actual complete discounted Stieltjes dividend value decreases with q,
    including time-zero, continuous, and all strict pre-ruin payments. -/
theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (x : ℝ) (D : ℝ≥0 → Ω → ℝ)
    (q₁ q₂ : ℝ) (hq : q₁ ≤ q₂) :
    dividendValue X q₂ x D ≤ dividendValue X q₁ x D := by
  change
    (∫⁻ ω : Ω, ∫⁻ t in paymentTimes (ruinTime X x D ω),
      ENNReal.ofReal (Real.exp (-(q₂ * t))) ∂(dividendMeasure D ω) ∂P) ≤
    (∫⁻ ω : Ω, ∫⁻ t in paymentTimes (ruinTime X x D ω),
      ENNReal.ofReal (Real.exp (-(q₁ * t))) ∂(dividendMeasure D ω) ∂P)
  apply MeasureTheory.lintegral_mono
  intro ω
  apply MeasureTheory.lintegral_mono_ae
  filter_upwards [MeasureTheory.ae_restrict_mem (paymentTimes_measurable _)] with t ht
  have ht0 : 0 ≤ t := ht.1
  have hmul : q₁ * t ≤ q₂ * t := mul_le_mul_of_nonneg_right hq ht0
  exact ENNReal.ofReal_le_ofReal (Real.exp_le_exp.mpr (neg_le_neg hmul))
