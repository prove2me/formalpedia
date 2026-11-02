-- Prove2me | solution 1 for AvramDividend.Classical.avram_wave5_04b_discounted_stieltjes_cell_le_left_endpoint_discount_mass
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-01T13:25:41.494357+00:00
-- url     : https://prove2.me/submissions/a8ccd6e8-e482-4463-9073-0495e9284df0

import Mathlib.Analysis.Complex.Exponential
import Mathlib.MeasureTheory.Integral.Lebesgue.Basic
open MeasureTheory Set
open scoped ENNReal

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

/-- Exact left-endpoint discount envelope for the full Stieltjes measure of a half-open cell. -/
theorem solution
    (q : ℝ) (hq : 0 ≤ q) (μ : Measure ℝ) (a b : ℝ) :
    (∫⁻ s in Ioc a b, ENNReal.ofReal (Real.exp (-(q * s))) ∂μ) ≤
      ENNReal.ofReal (Real.exp (-(q * a))) * μ (Ioc a b) := by
  calc
    (∫⁻ s in Ioc a b, ENNReal.ofReal (Real.exp (-(q * s))) ∂μ) ≤
        (∫⁻ s in Ioc a b, ENNReal.ofReal (Real.exp (-(q * a))) ∂μ) := by
      apply MeasureTheory.lintegral_mono_ae
      filter_upwards [MeasureTheory.ae_restrict_mem measurableSet_Ioc] with s hs
      have hqa : q * a ≤ q * s :=
        mul_le_mul_of_nonneg_left hs.1.le hq
      exact ENNReal.ofReal_le_ofReal (Real.exp_le_exp.mpr (neg_le_neg hqa))
    _ = ENNReal.ofReal (Real.exp (-(q * a))) * μ (Ioc a b) := by
      rw [MeasureTheory.lintegral_const]
      simp
