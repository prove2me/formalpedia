-- Prove2me | solution 2 for CohnElkies.saddleSourceWeightedCosineQuadraticRemainder_integral_eq
-- status  : ACCEPTED   (prove)
-- author  : @fizzyinc3
-- created : 2026-10-19T12:37:01.582361+00:00
-- url     : https://prove2.me/submissions/35bf6abe-6df3-4a69-9555-1bc7b29c52f0

import Mathlib
import Definitions.Def_SpherePacking
set_option autoImplicit true
open CohnElkies
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
set_option maxHeartbeats 800000
noncomputable section
open Filter Set MeasureTheory intervalIntegral
open scoped Topology


theorem solution
    (w : ℝ → ℝ) {b c : ℝ}
    (hbc : b ≤ c)
    (hw : ContinuousOn w (Icc b c))
    (u T : ℝ) :
    (∫ a in b..c,
      (w a : ℂ) * saddleSourceCosineQuadraticRemainder a u T) =
      (∫ a in b..c,
        (w a : ℂ) *
          (Complex.cos
            ((a : ℂ) *
              ((T : ℂ) + Complex.I * (u : ℂ))) - 1)) -
        (∫ a in b..c,
          (w a : ℂ) *
            ((Real.cosh (u * a) : ℂ) - 1)) +
        Complex.I *
          ((T * ∫ a in b..c,
            w a * a * Real.sinh (u * a) : ℝ) : ℂ) +
        ((T ^ 2 / 2 * ∫ a in b..c,
          w a * a ^ 2 * Real.cosh (u * a) : ℝ) : ℂ) := by
  have hw' : ContinuousOn (fun a : ℝ => (w a : ℂ)) (Set.Icc b c) :=
    Complex.continuous_ofReal.comp_continuousOn hw
  have i1 : IntervalIntegrable (fun a : ℝ => (w a : ℂ) *
      (Complex.cos ((a : ℂ) * ((T : ℂ) + Complex.I * (u : ℂ))) - 1)) MeasureTheory.volume b c :=
    (hw'.mul (Continuous.continuousOn (by fun_prop))).intervalIntegrable_of_Icc hbc
  have i2 : IntervalIntegrable (fun a : ℝ => (w a : ℂ) * ((Real.cosh (u * a) : ℂ) - 1))
      MeasureTheory.volume b c :=
    (hw'.mul (Continuous.continuousOn (by fun_prop))).intervalIntegrable_of_Icc hbc
  have i3 : IntervalIntegrable (fun a : ℝ => Complex.I * ((T * (w a * a * Real.sinh (u * a)) : ℝ) : ℂ))
      MeasureTheory.volume b c := by
    have : ContinuousOn (fun a : ℝ => T * (w a * a * Real.sinh (u * a))) (Set.Icc b c) :=
      continuousOn_const.mul ((hw.mul continuousOn_id).mul (Continuous.continuousOn (by fun_prop)))
    exact (continuousOn_const.mul (Complex.continuous_ofReal.comp_continuousOn this)).intervalIntegrable_of_Icc hbc
  have i4 : IntervalIntegrable (fun a : ℝ => (((T ^ 2 / 2 * (w a * a ^ 2 * Real.cosh (u * a))) : ℝ) : ℂ))
      MeasureTheory.volume b c := by
    have : ContinuousOn (fun a : ℝ => T ^ 2 / 2 * (w a * a ^ 2 * Real.cosh (u * a))) (Set.Icc b c) :=
      continuousOn_const.mul ((hw.mul (continuousOn_id.pow 2)).mul (Continuous.continuousOn (by fun_prop)))
    exact (Complex.continuous_ofReal.comp_continuousOn this).intervalIntegrable_of_Icc hbc
  have hpt : (fun a : ℝ => (w a : ℂ) * saddleSourceCosineQuadraticRemainder a u T) =
      fun a : ℝ => (w a : ℂ) * (Complex.cos ((a : ℂ) * ((T : ℂ) + Complex.I * (u : ℂ))) - 1) -
        (w a : ℂ) * ((Real.cosh (u * a) : ℂ) - 1) +
        Complex.I * ((T * (w a * a * Real.sinh (u * a)) : ℝ) : ℂ) +
        (((T ^ 2 / 2 * (w a * a ^ 2 * Real.cosh (u * a))) : ℝ) : ℂ) := by
    funext a
    unfold saddleSourceCosineQuadraticRemainder
    push_cast
    ring
  rw [hpt, intervalIntegral.integral_add ((i1.sub i2).add i3) i4,
    intervalIntegral.integral_add (i1.sub i2) i3, intervalIntegral.integral_sub i1 i2,
    intervalIntegral.integral_const_mul, intervalIntegral.integral_ofReal,
    intervalIntegral.integral_ofReal, intervalIntegral.integral_const_mul,
    intervalIntegral.integral_const_mul]

