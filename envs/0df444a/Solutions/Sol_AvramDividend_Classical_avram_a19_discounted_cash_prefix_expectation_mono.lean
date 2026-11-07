-- Prove2me | solution 1 for AvramDividend.Classical.avram_a19_discounted_cash_prefix_expectation_mono
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-06T06:28:51.764725+00:00
-- url     : https://prove2.me/submissions/9bdd03d2-67b6-4c7f-a4c7-0d48244b535c

import Mathlib
import Definitions.Def_AvramDividend_Classical_DividendStrategy
import Theorems.Thm_AvramDividend_Classical_avram_a19_discounted_cash_prefix_mono_finite

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory Set Filter AvramDividend.Classical
open scoped NNReal ENNReal
noncomputable section

/-- The pathwise strict cash monotonicity lifts to expectations under integrability. -/
theorem solution
    {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω)
    (D : ℝ≥0 → Ω → ℝ) (σ : Ω → ℝ≥0∞)
    (q s T : ℝ) (hst : s ≤ T)
    (hFinite : ∀ᵐ ω ∂P,
      (∫⁻ t in paymentTimes (σ ω) ∩ Iio T,
        ENNReal.ofReal (Real.exp (-(q * t))) ∂(dividendMeasure D ω)) ≠ ⊤)
    (hIs : Integrable (fun ω =>
      (∫⁻ t in paymentTimes (σ ω) ∩ Iio s,
        ENNReal.ofReal (Real.exp (-(q * t))) ∂(dividendMeasure D ω)).toReal) P)
    (hIT : Integrable (fun ω =>
      (∫⁻ t in paymentTimes (σ ω) ∩ Iio T,
        ENNReal.ofReal (Real.exp (-(q * t))) ∂(dividendMeasure D ω)).toReal) P) :
    (∫ ω, (∫⁻ t in paymentTimes (σ ω) ∩ Iio s,
      ENNReal.ofReal (Real.exp (-(q * t))) ∂(dividendMeasure D ω)).toReal ∂P) ≤
    (∫ ω, (∫⁻ t in paymentTimes (σ ω) ∩ Iio T,
      ENNReal.ofReal (Real.exp (-(q * t))) ∂(dividendMeasure D ω)).toReal ∂P) := by
  apply integral_mono_ae hIs hIT
  filter_upwards [hFinite] with ω hω
  exact avram_a19_discounted_cash_prefix_mono_finite D ω (σ ω) q s T hst hω
