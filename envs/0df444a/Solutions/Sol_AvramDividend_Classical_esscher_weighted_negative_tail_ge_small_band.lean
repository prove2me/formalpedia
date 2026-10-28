-- Prove2me | solution 1 for AvramDividend.Classical.esscher_weighted_negative_tail_ge_small_band
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-10-26T09:00:17.623932+00:00
-- url     : https://prove2.me/submissions/0a394215-9daa-49a2-b080-7d16db3b62de

import Mathlib.MeasureTheory.Measure.WithDensity
import Mathlib.MeasureTheory.Integral.Lebesgue.Basic
import Mathlib.Analysis.SpecialFunctions.ExpDeriv
import Mathlib.Tactic.Linarith

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory Set
open scoped ENNReal

/-- Restrict the weighted tail to jumps of magnitude below one and bound its density. -/
theorem solution
    (ν : Measure ℝ) (φ x : ℝ) (hφ : 0 ≤ φ) :
    ENNReal.ofReal (Real.exp (-φ)) * ν (Ioo (-1 : ℝ) (-x)) ≤
      (ν.withDensity (fun y : ℝ => ENNReal.ofReal (Real.exp (φ * y))))
        (Iio (-x)) := by
  let s : Set ℝ := Ioo (-1 : ℝ) (-x)
  let f : ℝ → ENNReal := fun y => ENNReal.ofReal (Real.exp (φ * y))
  have hfloor : ENNReal.ofReal (Real.exp (-φ)) ≤ ⨅ y ∈ s, f y := by
    refine le_iInf (fun y => le_iInf (fun hy => ?_))
    have hineq : (-φ) ≤ φ * y := by
      have h := mul_le_mul_of_nonneg_left hy.1.le hφ
      simpa only [mul_neg, mul_one] using h
    exact ENNReal.ofReal_le_ofReal (Real.exp_le_exp.mpr hineq)
  have hband : ENNReal.ofReal (Real.exp (-φ)) * ν s ≤
      ∫⁻ y in s, f y ∂ν := by
    exact (mul_le_mul_of_nonneg_right hfloor (show (0 : ENNReal) ≤ ν s by exact zero_le)).trans
      (iInf_mul_le_setLIntegral f measurableSet_Ioo)
  have hs : s ⊆ Iio (-x) := by
    intro y hy
    exact hy.2
  calc
    ENNReal.ofReal (Real.exp (-φ)) * ν (Ioo (-1 : ℝ) (-x))
        ≤ (ν.withDensity f) s := by
            simpa [s, f, withDensity_apply f measurableSet_Ioo] using hband
    _ ≤ (ν.withDensity f) (Iio (-x)) := measure_mono hs
