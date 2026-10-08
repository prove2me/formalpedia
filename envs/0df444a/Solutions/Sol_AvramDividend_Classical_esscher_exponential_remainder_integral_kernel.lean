-- Prove2me | solution 1 for AvramDividend.Classical.esscher_exponential_remainder_integral_kernel
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-10-08T06:34:41.646562+00:00
-- url     : https://prove2.me/submissions/0ea7f6a8-f522-4a18-a614-4a36facc3f72

import Mathlib

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory intervalIntegral Set

/-- Integrated Laplace exponential compensation, with no sign restrictions. -/
theorem solution (s z : ℝ) :
    s * (∫ t in (0 : ℝ)..z, (1 - Real.exp (-(s * t)))) =
      Real.exp (-(s * z)) - 1 + s * z := by
  have hecont : Continuous (fun t : ℝ => Real.exp (-(s * t))) := by
    fun_prop
  have heint :
      IntervalIntegrable (fun t : ℝ => Real.exp (-(s * t))) volume 0 z :=
    hecont.intervalIntegrable 0 z
  have hcone : IntervalIntegrable (fun _ : ℝ => (1 : ℝ)) volume 0 z :=
    continuous_const.intervalIntegrable 0 z
  have hscale :
      (-s) * (∫ t in (0 : ℝ)..z, Real.exp (-(s * t))) =
        Real.exp (-(s * z)) - 1 := by
    calc
      (-s) * (∫ t in (0 : ℝ)..z, Real.exp (-(s * t))) =
          ∫ u in (-s) * (0 : ℝ)..(-s) * z, Real.exp u := by
        simpa only [neg_mul] using
          (intervalIntegral.mul_integral_comp_mul_left
            (f := Real.exp) (a := (0 : ℝ)) (b := z) (c := -s))
      _ = Real.exp (-(s * z)) - 1 := by
        rw [mul_zero, integral_exp, Real.exp_zero]
        congr 1
        ring
  have hdecomp :
      (∫ t in (0 : ℝ)..z, (1 - Real.exp (-(s * t)))) =
        z - ∫ t in (0 : ℝ)..z, Real.exp (-(s * t)) := by
    rw [intervalIntegral.integral_sub hcone heint]
    simp
  rw [hdecomp]
  calc
    s * (z - ∫ t in (0 : ℝ)..z, Real.exp (-(s * t))) =
        s * z + (-s) * (∫ t in (0 : ℝ)..z, Real.exp (-(s * t))) := by ring
    _ = s * z + (Real.exp (-(s * z)) - 1) := by rw [hscale]
    _ = Real.exp (-(s * z)) - 1 + s * z := by ring
