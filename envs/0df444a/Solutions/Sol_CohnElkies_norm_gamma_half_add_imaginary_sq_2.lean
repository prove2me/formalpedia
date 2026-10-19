-- Prove2me | solution 2 for CohnElkies.norm_gamma_half_add_imaginary_sq
-- status  : ACCEPTED   (prove)
-- author  : @fizzyinc3
-- created : 2026-10-19T12:15:58.798106+00:00
-- url     : https://prove2.me/submissions/02d5ac3d-9bfa-403f-8f97-c6441f9dcbc2

import Mathlib
import Definitions.Def_SpherePacking
set_option autoImplicit true
open CohnElkies
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
set_option maxHeartbeats 800000
noncomputable section
open Filter MeasureTheory Set
open scoped FourierTransform Interval RealInnerProductSpace Topology


theorem solution (x : ℝ) :
    ‖Complex.Gamma ((1 / 2 : ℂ) + Complex.I * (x : ℂ))‖ ^ 2 =
      Real.pi / Real.cosh (Real.pi * x) := by
  set s : ℂ := (1 / 2 : ℂ) + Complex.I * (x : ℂ) with hs
  have h1 : 1 - s = (starRingEnd ℂ) s := by
    apply Complex.ext <;> simp [hs] <;> norm_num
  have h2 := Complex.Gamma_mul_Gamma_one_sub s
  rw [h1, Complex.Gamma_conj, Complex.mul_conj] at h2
  have h3 : Complex.sin (↑Real.pi * s) = ((Real.cosh (Real.pi * x) : ℝ) : ℂ) := by
    rw [show (↑Real.pi : ℂ) * s = ((Real.pi * x : ℝ) : ℂ) * Complex.I + ↑Real.pi / 2 by
      rw [hs]; push_cast; ring]
    rw [Complex.sin_add_pi_div_two, Complex.cos_mul_I, Complex.ofReal_cosh]
  rw [h3] at h2
  rw [← Complex.normSq_eq_norm_sq]
  have h4 : ((Complex.normSq (Complex.Gamma s) : ℝ) : ℂ) = ((Real.pi / Real.cosh (Real.pi * x) : ℝ) : ℂ) := by
    rw [h2]; push_cast; rfl
  exact_mod_cast h4

