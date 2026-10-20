-- Prove2me | solution 2 for CohnElkies.complexWallisPhaseKernel_re
-- status  : ACCEPTED   (prove)
-- author  : @fizzyinc3
-- created : 2026-10-19T12:33:10.801421+00:00
-- url     : https://prove2.me/submissions/7bd76bc9-dbd6-420c-8dfc-b4c0d597eed2

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


theorem solution (a u t : ℝ) :
    (complexWallisPhaseKernel
      ((a : ℂ) - Complex.I * (u : ℂ)) t).re =
        lowerWallisRegularizedPhaseKernel a u t := by
  unfold complexWallisPhaseKernel lowerWallisRegularizedPhaseKernel
  have h2 : (t : ℂ) ^ 2 = ((t ^ 2 : ℝ) : ℂ) := by push_cast; ring
  have he : Complex.exp (-((a : ℂ) - Complex.I * (u : ℂ)) * (t : ℂ)) =
      ((Real.exp (-a * t) : ℝ) : ℂ) * (((Real.cos (u * t)) : ℝ) + ((Real.sin (u * t) : ℝ) : ℂ) * Complex.I) := by
    rw [show -((a : ℂ) - Complex.I * (u : ℂ)) * (t : ℂ) = ((-a * t : ℝ) : ℂ) + ((u * t : ℝ) : ℂ) * Complex.I by push_cast; ring,
      Complex.exp_add_mul_I, ← Complex.ofReal_exp, ← Complex.ofReal_cos, ← Complex.ofReal_sin]
  have he2 : Complex.exp (-(t : ℂ)) = ((Real.exp (-t) : ℝ) : ℂ) := by rw [Complex.ofReal_exp, Complex.ofReal_neg]
  rw [h2, Complex.div_ofReal_re, he, he2]
  congr 1
  simp only [Complex.sub_re, Complex.mul_re, Complex.add_re, Complex.ofReal_re, Complex.ofReal_im, Complex.I_re, Complex.I_im, Complex.one_re, Complex.one_im, Complex.sub_im, Complex.mul_im, Complex.add_im]
  ring

