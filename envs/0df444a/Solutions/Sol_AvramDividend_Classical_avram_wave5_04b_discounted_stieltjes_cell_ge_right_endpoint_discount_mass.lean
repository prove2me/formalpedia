-- Prove2me | solution 1 for AvramDividend.Classical.avram_wave5_04b_discounted_stieltjes_cell_ge_right_endpoint_discount_mass
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-01T13:45:47.395201+00:00
-- url     : https://prove2.me/submissions/97292e0d-7297-4579-8e19-c9664d66dbc0

import Mathlib.Analysis.Complex.Exponential
import Mathlib.MeasureTheory.Integral.Lebesgue.Basic
open MeasureTheory Set
open scoped ENNReal

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

/-- Exact right-endpoint lower discount envelope for the complete Stieltjes measure of a half-open time cell, with no atomicity or finite-mass assumptions. -/
theorem solution
    (q : ℝ) (hq : 0 ≤ q) (μ : Measure ℝ) (a b : ℝ) :
    ENNReal.ofReal (Real.exp (-(q * b))) * μ (Ioc a b) ≤
      (∫⁻ s in Ioc a b, ENNReal.ofReal (Real.exp (-(q * s))) ∂μ) := by
  calc
    ENNReal.ofReal (Real.exp (-(q * b))) * μ (Ioc a b) =
        (∫⁻ s in Ioc a b, ENNReal.ofReal (Real.exp (-(q * b))) ∂μ) := by
      rw [MeasureTheory.lintegral_const]
      simp
    _ ≤ (∫⁻ s in Ioc a b, ENNReal.ofReal (Real.exp (-(q * s))) ∂μ) := by
      apply MeasureTheory.lintegral_mono_ae
      filter_upwards [MeasureTheory.ae_restrict_mem measurableSet_Ioc] with s hs
      have hqb : q * s ≤ q * b :=
        mul_le_mul_of_nonneg_left hs.2 hq
      exact ENNReal.ofReal_le_ofReal (Real.exp_le_exp.mpr (neg_le_neg hqb))
