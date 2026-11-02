-- Prove2me | solution 1 for AvramDividend.Classical.avram_wave5_04c_C1_negative_jump_increment_FTC
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-01T15:00:25.399625+00:00
-- url     : https://prove2.me/submissions/5f7d8715-a212-4888-98ee-5d135b560c46

import Mathlib
set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

set_option autoImplicit false
open MeasureTheory Set

/-! Deterministic C1 negative-jump increment as an exact derivative integral. -/
theorem solution (w : ℝ → ℝ) (hwC1 : ContDiff ℝ 1 w)
    (y R : ℝ) :
    (∫ r in (0 : ℝ)..R, deriv w (y - r)) = w y - w (y - R) := by
  let g : ℝ → ℝ := fun r => w (y - r)
  have hdw : Differentiable ℝ w := hwC1.differentiable (by norm_num)
  have hdg : Differentiable ℝ g := by
    intro r
    exact (hdw (y - r)).comp r
      (((hasDerivAt_const r y).sub (hasDerivAt_id r)).differentiableAt)
  have hderiv (r : ℝ) : deriv g r = -deriv w (y - r) := by
    have hh : HasDerivAt g (deriv w (y - r) * (0 - 1)) r :=
      ((hdw (y - r)).hasDerivAt).comp r
        ((hasDerivAt_const r y).sub (hasDerivAt_id r))
    convert hh.deriv using 1 <;> ring
  have hc : Continuous (deriv g) := by
    have hw' := hwC1.continuous_deriv (by norm_num)
    have hgEq : deriv g = fun r => -deriv w (y - r) := funext hderiv
    rw [hgEq]
    exact (hw'.comp (continuous_const.sub continuous_id)).neg
  have hi : IntervalIntegrable (deriv g) volume 0 R :=
    hc.intervalIntegrable _ _
  have hftc : (∫ r in (0 : ℝ)..R, deriv g r) = g R - g 0 :=
    intervalIntegral.integral_deriv_eq_sub (fun t ht => hdg.differentiableAt) hi
  have heq : (∫ r in (0 : ℝ)..R, deriv g r) =
      -(∫ r in (0 : ℝ)..R, deriv w (y - r)) := by
    simp_rw [hderiv]
    simp
  calc
    (∫ r in (0 : ℝ)..R, deriv w (y - r)) =
        -(∫ r in (0 : ℝ)..R, deriv g r) := by rw [heq]; ring
    _ = w y - w (y - R) := by rw [hftc]; simp [g]
