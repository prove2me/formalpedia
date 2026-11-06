-- Prove2me | solution 1 for AvramDividend.Classical.avram_p4_f3_original_time_discount_preserves_physical_L2_energy
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-05T19:34:19.577148+00:00
-- url     : https://prove2.me/submissions/c916bc9f-7d1e-4a92-b134-7a453ce53101

import Mathlib.Analysis.Complex.Exponential
import Mathlib.MeasureTheory.Integral.Lebesgue.Basic
set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory
open scoped ENNReal NNReal
noncomputable section

/-- Physical nonnegative time discounting preserves any finite L² source energy. -/
theorem solution
    {Ω : Type*} [MeasurableSpace Ω]
    (q : ℝ) (hq : 0 ≤ q)
    (μ : Measure (ℝ≥0 × Ω))
    (F : ℝ≥0 × Ω → ℝ)
    (hF : (∫⁻ p, ENNReal.ofReal ((F p) ^ 2) ∂μ) < ⊤) :
    (∫⁻ p, ENNReal.ofReal
      ((Real.exp (-(q * (p.1 : ℝ))) * F p) ^ 2) ∂μ) < ⊤ := by
  have hbound :
      (∫⁻ p, ENNReal.ofReal
        ((Real.exp (-(q * (p.1 : ℝ))) * F p) ^ 2) ∂μ) ≤
      (∫⁻ p, ENNReal.ofReal ((F p) ^ 2) ∂μ) := by
    apply lintegral_mono
    intro p
    have ht : 0 ≤ (p.1 : ℝ) := p.1.property
    have hnonpos : -(q * (p.1 : ℝ)) ≤ 0 := by nlinarith
    have hpos : 0 < Real.exp (-(q * (p.1 : ℝ))) := Real.exp_pos _
    have hle : Real.exp (-(q * (p.1 : ℝ))) ≤ 1 := by
      rw [← Real.exp_zero]
      exact Real.exp_le_exp.mpr hnonpos
    have hsq : (Real.exp (-(q * (p.1 : ℝ)))) ^ 2 ≤ 1 := by nlinarith
    apply ENNReal.ofReal_le_ofReal
    calc
      (Real.exp (-(q * (p.1 : ℝ))) * F p) ^ 2 =
          (Real.exp (-(q * (p.1 : ℝ)))) ^ 2 * (F p) ^ 2 := by ring
      _ ≤ 1 * (F p) ^ 2 := mul_le_mul_of_nonneg_right hsq (sq_nonneg _)
      _ = (F p) ^ 2 := one_mul _
  exact lt_of_le_of_lt hbound hF
