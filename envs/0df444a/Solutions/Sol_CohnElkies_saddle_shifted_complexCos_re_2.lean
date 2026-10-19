-- Prove2me | solution 2 for CohnElkies.saddle_shifted_complexCos_re
-- status  : ACCEPTED   (prove)
-- author  : @fizzyinc3
-- created : 2026-10-19T12:05:27.547953+00:00
-- url     : https://prove2.me/submissions/44416340-12d0-4936-ba4a-a05dae81c1a6

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
    (a T u : ℝ) :
    (Complex.cos
      ((a : ℂ) * ((T : ℂ) + Complex.I * (u : ℂ)))).re =
      Real.cos (a * T) * Real.cosh (a * u) := by
  have h : (a : ℂ) * ((T : ℂ) + Complex.I * (u : ℂ)) = ((a * T : ℝ) : ℂ) + ((a * u : ℝ) : ℂ) * Complex.I := by
    push_cast; ring
  rw [h, Complex.cos_add_mul_I, ← Complex.ofReal_cos, ← Complex.ofReal_cosh, ← Complex.ofReal_sin,
    ← Complex.ofReal_sinh]
  simp only [Complex.sub_re, Complex.mul_re, Complex.mul_im, Complex.ofReal_re, Complex.ofReal_im,
    Complex.I_re, Complex.I_im]
  ring

