-- Prove2me | solution 1 for AvramDividend.Classical.avram_wave6_08_discounted_right_endpoint_cell_upper_error
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-02T06:39:11.248962+00:00
-- url     : https://prove2.me/submissions/129b7ba8-d758-46cb-b380-75326d8ec86d

import Mathlib.Analysis.Complex.Exponential
import Mathlib.MeasureTheory.Integral.Lebesgue.Basic
import Mathlib.Tactic.Linarith

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory Set
open scoped ENNReal

theorem solution
    (q : ℝ) (hq : 0 ≤ q) (μ : Measure ℝ) (a b : ℝ)
    (ha : 0 ≤ a) (hab : a ≤ b) :
    (∫⁻ s in Ioc a b, ENNReal.ofReal (Real.exp (-(q * s))) ∂μ) ≤
      ENNReal.ofReal (Real.exp (-(q * b)) + q * (b - a)) * μ (Ioc a b) := by
  have hpoint (s : ℝ) (hs : s ∈ Ioc a b) :
      Real.exp (-(q * s)) ≤ Real.exp (-(q * b)) + q * (b - a) := by
    have hsn : 0 ≤ s := le_trans ha hs.1.le
    have hqs : 0 ≤ q * s := mul_nonneg hq hsn
    have hz : 0 ≤ q * (b - s) := mul_nonneg hq (sub_nonneg.mpr hs.2)
    have hres : Real.exp (-(q * s)) ≤ 1 :=
      Real.exp_le_one_iff.mpr (neg_nonpos.mpr hqs)
    have hbase : 1 - q * (b - s) ≤ Real.exp (-(q * (b - s))) := by
      have h := Real.add_one_le_exp (-(q * (b - s)))
      linarith
    have hfact : Real.exp (-(q * b)) =
        Real.exp (-(q * s)) * Real.exp (-(q * (b - s))) := by
      rw [← Real.exp_add]
      congr 1
      ring
    have hpiece : Real.exp (-(q * s)) * (1 - q * (b - s)) ≤
        Real.exp (-(q * b)) := by
      rw [hfact]
      exact mul_le_mul_of_nonneg_left hbase (Real.exp_pos _).le
    have hmult : Real.exp (-(q * s)) * (q * (b - s)) ≤ q * (b - s) := by
      nlinarith [mul_nonneg (sub_nonneg.mpr hres) hz]
    have hdiff : q * (b - s) ≤ q * (b - a) :=
      mul_le_mul_of_nonneg_left (sub_le_sub_left hs.1.le b) hq
    nlinarith
  calc
    (∫⁻ s in Ioc a b, ENNReal.ofReal (Real.exp (-(q * s))) ∂μ) ≤
        (∫⁻ s in Ioc a b,
          ENNReal.ofReal (Real.exp (-(q * b)) + q * (b - a)) ∂μ) := by
      apply MeasureTheory.lintegral_mono_ae
      filter_upwards [MeasureTheory.ae_restrict_mem measurableSet_Ioc] with s hs
      exact ENNReal.ofReal_le_ofReal (hpoint s hs)
    _ = ENNReal.ofReal (Real.exp (-(q * b)) + q * (b - a)) * μ (Ioc a b) := by
      rw [MeasureTheory.lintegral_const]
      simp
