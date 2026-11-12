-- Prove2me | solution 1 for AvramDividend.Classical.avram_gledger96_measurable_stopped_cash_discount_lower_mass
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-11T12:22:23.768113+00:00
-- url     : https://prove2.me/submissions/0b9b2f72-a2d2-4b0d-aca2-499209efd2c6

import Mathlib
set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory Set
open scoped NNReal ENNReal
noncomputable section

theorem solution
    (q : ℝ) (hq : 0 ≤ q) (μ : Measure ℝ)
    (S : Set ℝ) (hS : MeasurableSet S)
    (b : ℝ) (hSb : ∀ t ∈ S, t ≤ b) :
    ENNReal.ofReal (Real.exp (-(q * b))) * μ S ≤
      (∫⁻ t in S, ENNReal.ofReal (Real.exp (-(q * t))) ∂μ) := by
  have hpoint : ∀ t ∈ S,
      ENNReal.ofReal (Real.exp (-(q * b))) ≤
        ENNReal.ofReal (Real.exp (-(q * t))) := by
    intro t ht
    apply ENNReal.ofReal_le_ofReal
    apply Real.exp_le_exp.mpr
    nlinarith [mul_le_mul_of_nonneg_left (hSb t ht) hq]
  have ha : ∀ᵐ t ∂μ.restrict S,
      ENNReal.ofReal (Real.exp (-(q * b))) ≤
        ENNReal.ofReal (Real.exp (-(q * t))) := by
    filter_upwards [ae_restrict_mem hS] with t ht
    exact hpoint t ht
  have hmono := lintegral_mono_ae ha
  simpa [Measure.restrict_apply, hS, lintegral_const, mul_comm] using hmono
