-- Prove2me | solution 1 for AvramDividend.Classical.avram_p3_c_bvchain_public_discount_left_full_measure_le
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-03T20:12:04.328602+00:00
-- url     : https://prove2.me/submissions/195497df-f8a7-4670-9ca3-030c89075614

import Mathlib.MeasureTheory.Integral.Lebesgue.Basic
import Mathlib.MeasureTheory.Measure.Restrict
import Mathlib.Data.ENNReal.Real
import Mathlib.Analysis.Complex.Exponential

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory Set
open scoped ENNReal

/-- Generic complete discounted interval-mass bound, publicly reusable. -/
theorem solution (q : ℝ) (hq : 0 ≤ q) (μ : Measure ℝ) (a b : ℝ) :
    (∫⁻ t in Ioc a b, ENNReal.ofReal (Real.exp (-(q * t))) ∂μ) ≤
      ENNReal.ofReal (Real.exp (-(q * a))) * μ (Ioc a b) := by
  calc
    (∫⁻ t in Ioc a b, ENNReal.ofReal (Real.exp (-(q * t))) ∂μ) ≤
        (∫⁻ t in Ioc a b,
          ENNReal.ofReal (Real.exp (-(q * a))) ∂μ) := by
      apply MeasureTheory.lintegral_mono_ae
      filter_upwards [MeasureTheory.ae_restrict_mem measurableSet_Ioc]
        with t ht
      apply ENNReal.ofReal_le_ofReal
      apply Real.exp_le_exp.mpr
      have hqa : q * a ≤ q * t :=
        mul_le_mul_of_nonneg_left ht.1.le hq
      linarith only [hqa]
    _ = ENNReal.ofReal (Real.exp (-(q * a))) * μ (Ioc a b) := by
      rw [MeasureTheory.lintegral_const]
      simp [mul_comm]
