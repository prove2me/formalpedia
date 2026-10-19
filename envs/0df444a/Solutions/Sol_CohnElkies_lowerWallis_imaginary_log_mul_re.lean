-- Prove2me | solution 1 for CohnElkies.lowerWallis_imaginary_log_mul_re
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-10-19T11:37:25.301796+00:00
-- url     : https://prove2.me/submissions/52c43e48-9d0d-4e60-ba1e-e6391210d375

import Mathlib
import Definitions.Def_SpherePacking

set_option autoImplicit true
open CohnElkies
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
set_option maxHeartbeats 800000
noncomputable section
open Filter MeasureTheory Set
open scoped Interval Topology
namespace CohnElkies
theorem _root_.solution (u : ℝ) :
    ((-Complex.I * (u : ℂ)) *
      Complex.log (-Complex.I * (u : ℂ))).re =
        -Real.pi * |u| / 2 := by
  by_cases hzero : u = 0
  · subst u
    simp
  rcases lt_or_gt_of_ne hzero with hnegative | hpositive
  · have harg :
        Complex.arg (-Complex.I * (u : ℂ)) =
          Real.pi / 2 := by
      apply Complex.arg_eq_pi_div_two_iff.mpr
      constructor
      · simp
      · simpa using! (neg_pos.mpr hnegative)
    rw [Complex.mul_re, Complex.log_im, harg,
      abs_of_neg hnegative]
    simp
    ring
  · have harg :
        Complex.arg (-Complex.I * (u : ℂ)) =
          -(Real.pi / 2) := by
      apply Complex.arg_eq_neg_pi_div_two_iff.mpr
      constructor
      · simp
      · simpa using! (neg_neg_of_pos hpositive)
    rw [Complex.mul_re, Complex.log_im, harg,
      abs_of_pos hpositive]
    simp
    ring
end CohnElkies
