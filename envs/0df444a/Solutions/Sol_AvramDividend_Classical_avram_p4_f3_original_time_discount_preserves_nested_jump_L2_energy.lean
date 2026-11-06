-- Prove2me | solution 1 for AvramDividend.Classical.avram_p4_f3_original_time_discount_preserves_nested_jump_L2_energy
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-05T19:41:15.201217+00:00
-- url     : https://prove2.me/submissions/5c041164-1326-467b-b67a-3833c155f9b6

import Mathlib.Analysis.Complex.Exponential
import Mathlib.MeasureTheory.Integral.Lebesgue.Basic
set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory
open scoped NNReal ENNReal
noncomputable section

/-- Actual nonnegative-time discount preserves nested quadratic jump energy. -/
theorem solution
    {Ω A : Type*} [MeasurableSpace Ω] [MeasurableSpace A]
    (q : ℝ) (hq : 0 ≤ q)
    (μ : Measure (ℝ≥0 × Ω)) (ν : Measure A)
    (F : (ℝ≥0 × Ω) → A → ℝ)
    (hF : (∫⁻ p, (∫⁻ z, ENNReal.ofReal ((F p z) ^ 2) ∂ν) ∂μ) < ⊤) :
    (∫⁻ p, (∫⁻ z, ENNReal.ofReal
      ((Real.exp (-(q * (p.1 : ℝ))) * F p z) ^ 2) ∂ν) ∂μ) < ⊤ := by
  have hbound :
      (∫⁻ p, (∫⁻ z, ENNReal.ofReal
        ((Real.exp (-(q * (p.1 : ℝ))) * F p z) ^ 2) ∂ν) ∂μ) ≤
      (∫⁻ p, (∫⁻ z, ENNReal.ofReal ((F p z) ^ 2) ∂ν) ∂μ) := by
    apply lintegral_mono
    intro p
    apply lintegral_mono
    intro z
    have ht : 0 ≤ (p.1 : ℝ) := p.1.property
    have hnonpos : -(q * (p.1 : ℝ)) ≤ 0 := by nlinarith
    have hpos : 0 < Real.exp (-(q * (p.1 : ℝ))) := Real.exp_pos _
    have hle : Real.exp (-(q * (p.1 : ℝ))) ≤ 1 := by
      rw [← Real.exp_zero]
      exact Real.exp_le_exp.mpr hnonpos
    have hsq : (Real.exp (-(q * (p.1 : ℝ)))) ^ 2 ≤ 1 := by nlinarith
    apply ENNReal.ofReal_le_ofReal
    calc
      (Real.exp (-(q * (p.1 : ℝ))) * F p z) ^ 2 =
          (Real.exp (-(q * (p.1 : ℝ)))) ^ 2 * (F p z) ^ 2 := by ring
      _ ≤ 1 * (F p z) ^ 2 := mul_le_mul_of_nonneg_right hsq (sq_nonneg _)
      _ = (F p z) ^ 2 := one_mul _
  exact lt_of_le_of_lt hbound hF
