-- Prove2me | solution 1 for AvramDividend.Classical.avram_wave7_11_expected_stieltjes_antitone_in_discount_rate
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-02T16:58:09.784676+00:00
-- url     : https://prove2.me/submissions/b0327386-00f7-420a-a795-fc0a676cdf6a

import Definitions.Def_AvramDividend_Classical_DividendStrategy
import Theorems.Thm_AvramDividend_Classical_avram_wave7_11_original_discounted_stieltjes_antitone_in_rate
import Mathlib.Analysis.Complex.Exponential
import Mathlib.MeasureTheory.MeasurableSpace.Defs

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory Set
open scoped NNReal ENNReal
open AvramDividend.Classical

/-- The expected original finite-horizon Stieltjes dividend value is
    antitone in the discount rate, retaining all ruin-time payment atoms. -/
theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    (D : ℝ≥0 → Ω → ℝ) (σ : Ω → ℝ≥0∞)
    (T q₁ q₂ : ℝ) (hq : q₁ ≤ q₂) :
    (∫⁻ ω, ∫⁻ t in paymentTimes (σ ω) ∩ Iic T,
      ENNReal.ofReal (Real.exp (-(q₂ * t))) ∂(dividendMeasure D ω) ∂P) ≤
    (∫⁻ ω, ∫⁻ t in paymentTimes (σ ω) ∩ Iic T,
      ENNReal.ofReal (Real.exp (-(q₁ * t))) ∂(dividendMeasure D ω) ∂P) := by
  apply lintegral_mono
  intro ω
  exact avram_wave7_11_original_discounted_stieltjes_antitone_in_rate
    D ω (σ ω) T q₁ q₂ hq
