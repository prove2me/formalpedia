-- Prove2me | solution 1 for AvramDividend.Classical.esscher_weighted_negative_tail_le_unweighted
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-10-26T09:16:49.45993+00:00
-- url     : https://prove2.me/submissions/fbd96b45-66ea-476f-92e4-85680471390a

import Mathlib.MeasureTheory.Measure.WithDensity
import Mathlib.MeasureTheory.Integral.Lebesgue.Basic
import Mathlib.Analysis.SpecialFunctions.ExpDeriv
import Mathlib.Tactic.Linarith

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory Set
open scoped ENNReal

/-- A nonnegative Esscher tilt discounts every strictly negative jump. -/
theorem solution
    (ν : Measure ℝ) (φ x : ℝ) (hφ : 0 ≤ φ) (hx : 0 < x) :
    (ν.withDensity (fun y : ℝ => ENNReal.ofReal (Real.exp (φ * y))))
        (Iio (-x)) ≤ ν (Iio (-x)) := by
  let s : Set ℝ := Iio (-x)
  have hpoint : ∀ y ∈ s,
      ENNReal.ofReal (Real.exp (φ * y)) ≤ (1 : ENNReal) := by
    intro y hy
    have hyneg : y ≤ 0 := by
      have : y < -x := hy
      linarith
    have hφy : φ * y ≤ 0 := mul_nonpos_of_nonneg_of_nonpos hφ hyneg
    have hExp : Real.exp (φ * y) ≤ 1 := Real.exp_le_one_iff.mpr hφy
    calc
      ENNReal.ofReal (Real.exp (φ * y)) ≤ ENNReal.ofReal (1 : ℝ) :=
        ENNReal.ofReal_le_ofReal hExp
      _ = 1 := by norm_num
  calc
    (ν.withDensity (fun y : ℝ => ENNReal.ofReal (Real.exp (φ * y)))) (Iio (-x))
        = ∫⁻ y in s, ENNReal.ofReal (Real.exp (φ * y)) ∂ν := by
            exact withDensity_apply _ measurableSet_Iio
    _ ≤ ∫⁻ y in s, (1 : ENNReal) ∂ν :=
      setLIntegral_mono' measurableSet_Iio hpoint
    _ = ν (Iio (-x)) := by simpa only [s] using setLIntegral_one s
