-- Prove2me | solution 1 for AvramDividend.Classical.avram_wave7_11_original_expected_stieltjes_discount_horizon_comparison
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-02T17:25:48.452243+00:00
-- url     : https://prove2.me/submissions/b7b63f48-c29b-4722-a7d5-ec91a8cc9e42

import Definitions.Def_AvramDividend_Classical_DividendStrategy
import Theorems.Thm_AvramDividend_Classical_avram_wave7_11_expected_stieltjes_antitone_in_discount_rate
import Theorems.Thm_AvramDividend_Classical_avram_wave7_11_original_expected_stieltjes_horizon_mono
import Mathlib.Analysis.Complex.Exponential
import Mathlib.MeasureTheory.MeasurableSpace.Defs

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory Set
open scoped NNReal ENNReal
open AvramDividend.Classical

/-- The original expected finite-horizon payout decreases with the
    discount rate and increases with the real observation horizon. -/
theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    (D : ℝ≥0 → Ω → ℝ) (σ : Ω → ℝ≥0∞)
    (q₁ q₂ T U : ℝ) (hq : q₁ ≤ q₂) (hTU : T ≤ U) :
    (∫⁻ ω, ∫⁻ t in paymentTimes (σ ω) ∩ Iic T,
      ENNReal.ofReal (Real.exp (-(q₂ * t))) ∂(dividendMeasure D ω) ∂P) ≤
    (∫⁻ ω, ∫⁻ t in paymentTimes (σ ω) ∩ Iic U,
      ENNReal.ofReal (Real.exp (-(q₁ * t))) ∂(dividendMeasure D ω) ∂P) := by
  calc
    (∫⁻ ω, ∫⁻ t in paymentTimes (σ ω) ∩ Iic T,
      ENNReal.ofReal (Real.exp (-(q₂ * t))) ∂(dividendMeasure D ω) ∂P) ≤
    (∫⁻ ω, ∫⁻ t in paymentTimes (σ ω) ∩ Iic T,
      ENNReal.ofReal (Real.exp (-(q₁ * t))) ∂(dividendMeasure D ω) ∂P) :=
        avram_wave7_11_expected_stieltjes_antitone_in_discount_rate
          D σ T q₁ q₂ hq
    _ ≤ (∫⁻ ω, ∫⁻ t in paymentTimes (σ ω) ∩ Iic U,
      ENNReal.ofReal (Real.exp (-(q₁ * t))) ∂(dividendMeasure D ω) ∂P) :=
        avram_wave7_11_original_expected_stieltjes_horizon_mono
          D σ q₁ T U hTU
