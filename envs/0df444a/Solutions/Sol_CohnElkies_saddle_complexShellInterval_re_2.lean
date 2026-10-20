-- Prove2me | solution 2 for CohnElkies.saddle_complexShellInterval_re
-- status  : ACCEPTED   (prove)
-- author  : @fizzyinc3
-- created : 2026-10-19T12:29:23.436988+00:00
-- url     : https://prove2.me/submissions/d9beee34-33f6-4cfb-8d64-6219fd897d71

import Mathlib
import Definitions.Def_SpherePacking
set_option autoImplicit true
open CohnElkies
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
set_option maxHeartbeats 800000
noncomputable section
open Filter MeasureTheory Set
open scoped Topology


theorem solution
    (w : ℝ → ℝ) {a b : ℝ}
    (hab : a ≤ b)
    (hw : ContinuousOn w (Icc a b))
    (T u : ℝ) :
    (∫ x in a..b,
      (w x : ℂ) *
        (Complex.cos
          ((x : ℂ) *
            ((T : ℂ) + Complex.I * (u : ℂ))) - 1)).re =
      ∫ x in a..b,
        w x *
          (Real.cos (x * T) * Real.cosh (x * u) - 1) := by
  have hw' : ContinuousOn w (Set.uIcc a b) := by rw [Set.uIcc_of_le hab]; exact hw
  have hint : IntervalIntegrable (fun x : ℝ => (w x : ℂ) *
      (Complex.cos ((x : ℂ) * ((T : ℂ) + Complex.I * (u : ℂ))) - 1)) MeasureTheory.volume a b :=
    ((Complex.continuous_ofReal.comp_continuousOn hw').mul (by fun_prop)).intervalIntegrable
  rw [← Complex.reCLM_apply, ← ContinuousLinearMap.intervalIntegral_comp_comm _ hint]
  congr 1; funext x
  have e : (x : ℂ) * ((T : ℂ) + Complex.I * (u : ℂ)) = ((x * T : ℝ) : ℂ) + ((x * u : ℝ) : ℂ) * Complex.I := by
    push_cast; ring
  rw [Complex.reCLM_apply, e, Complex.cos_add_mul_I, ← Complex.ofReal_cos, ← Complex.ofReal_cosh,
    ← Complex.ofReal_sin, ← Complex.ofReal_sinh]
  simp only [Complex.sub_re, Complex.mul_re, Complex.mul_im, Complex.ofReal_re, Complex.ofReal_im,
    Complex.I_re, Complex.I_im, Complex.one_re, Complex.one_im, Complex.sub_im]
  ring

