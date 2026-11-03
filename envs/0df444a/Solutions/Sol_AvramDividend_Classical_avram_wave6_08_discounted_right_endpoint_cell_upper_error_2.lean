-- Prove2me | solution 2 for AvramDividend.Classical.avram_wave6_08_discounted_right_endpoint_cell_upper_error
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-02T06:39:23.541439+00:00
-- url     : https://prove2.me/submissions/a4f2861c-dfa1-4b50-9448-2b63e7f6bc13

import Mathlib.Analysis.Complex.Exponential
import Mathlib.MeasureTheory.Integral.Lebesgue.Basic

open MeasureTheory Set
open scoped ENNReal

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

/-- Quantitative right-endpoint discount quadrature bound for an arbitrary
Stieltjes cell, including singular-continuous and atomic measure mass. -/
theorem solution
    (q : ℝ) (hq : 0 ≤ q) (μ : Measure ℝ) (a b : ℝ)
    (ha : 0 ≤ a) (hab : a ≤ b) :
    (∫⁻ s in Ioc a b, ENNReal.ofReal (Real.exp (-(q * s))) ∂μ) ≤
      ENNReal.ofReal (Real.exp (-(q * b)) + q * (b - a)) * μ (Ioc a b) := by
  calc
    (∫⁻ s in Ioc a b, ENNReal.ofReal (Real.exp (-(q * s))) ∂μ) ≤
        (∫⁻ s in Ioc a b,
          ENNReal.ofReal (Real.exp (-(q * b)) + q * (b - a)) ∂μ) := by
      apply MeasureTheory.lintegral_mono_ae
      filter_upwards [MeasureTheory.ae_restrict_mem measurableSet_Ioc] with s hs
      have hs0 : 0 ≤ s := le_trans ha (le_of_lt hs.1)
      have hqs : 0 ≤ q * s := mul_nonneg hq hs0
      have hv : 0 ≤ q * (b - s) :=
        mul_nonneg hq (sub_nonneg.mpr hs.2)
      have hvle : q * (b - s) ≤ q * (b - a) := by
        have hmul := mul_le_mul_of_nonneg_left (le_of_lt hs.1) hq
        nlinarith
      have he1 : Real.exp (-(q * s)) ≤ 1 := by
        have h := Real.exp_le_exp.mpr (show -(q * s) ≤ (0 : ℝ) by linarith)
        simpa using h
      have he2 : Real.exp (-(q * (b - s))) ≤ 1 := by
        have h := Real.exp_le_exp.mpr
          (show -(q * (b - s)) ≤ (0 : ℝ) by linarith)
        simpa using h
      have hstep : 1 - Real.exp (-(q * (b - s))) ≤ q * (b - s) := by
        have h := Real.add_one_le_exp (-(q * (b - s)))
        linarith
      have heq : Real.exp (-(q * b)) =
          Real.exp (-(q * s)) * Real.exp (-(q * (b - s))) := by
        rw [← Real.exp_add]
        congr 1
        ring
      have hprod : Real.exp (-(q * s)) *
          (1 - Real.exp (-(q * (b - s)))) ≤
          1 - Real.exp (-(q * (b - s))) := by
        have h := mul_le_mul_of_nonneg_right he1 (sub_nonneg.mpr he2)
        nlinarith
      have hfirst : Real.exp (-(q * s)) ≤
          Real.exp (-(q * b)) + (1 - Real.exp (-(q * (b - s)))) := by
        rw [heq]
        nlinarith
      have hreal : Real.exp (-(q * s)) ≤
          Real.exp (-(q * b)) + q * (b - a) := by
        linarith
      exact ENNReal.ofReal_le_ofReal hreal
    _ = ENNReal.ofReal (Real.exp (-(q * b)) + q * (b - a)) *
          μ (Ioc a b) := by
      rw [MeasureTheory.lintegral_const]
      simp
