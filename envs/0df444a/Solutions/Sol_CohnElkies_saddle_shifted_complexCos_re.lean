-- Prove2me | solution 1 for CohnElkies.saddle_shifted_complexCos_re
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-10-19T11:37:27.275309+00:00
-- url     : https://prove2.me/submissions/7d4c6878-477d-4da1-8749-d70e661aeb61

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
namespace CohnElkies
theorem _root_.solution
    (a T u : ℝ) :
    (Complex.cos
      ((a : ℂ) * ((T : ℂ) + Complex.I * (u : ℂ)))).re =
      Real.cos (a * T) * Real.cosh (a * u) := by
  have harg :
      (a : ℂ) * ((T : ℂ) + Complex.I * (u : ℂ)) =
        ((a * T : ℝ) : ℂ) +
          ((a * u : ℝ) : ℂ) * Complex.I := by
    push_cast
    ring
  rw [harg, Complex.cos_add, Complex.cos_mul_I,
    Complex.sin_mul_I, ← Complex.ofReal_cos,
    ← Complex.ofReal_cosh, ← Complex.ofReal_sin,
    ← Complex.ofReal_sinh]
  simp only [Complex.sub_re, Complex.mul_re,
    Complex.ofReal_re, Complex.ofReal_im,
    Complex.I_re, Complex.I_im,
    mul_zero, zero_mul, sub_zero, mul_one]
end CohnElkies
