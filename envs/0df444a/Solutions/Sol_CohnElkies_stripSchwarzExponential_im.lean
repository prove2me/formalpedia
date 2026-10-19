-- Prove2me | solution 1 for CohnElkies.stripSchwarzExponential_im
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-10-19T11:37:21.360486+00:00
-- url     : https://prove2.me/submissions/f5d0a760-c3c6-43e7-adc1-43b657c31a97

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
theorem _root_.solution (ℓ : ℝ) (z : ℂ) (y : ℝ) :
    (stripSchwarzExponential ℓ z y).im =
      Real.exp (Real.pi * (z.re - y) / (2 * ℓ)) *
        Real.sin (Real.pi * (z.im + ℓ) / (2 * ℓ)) := by
  unfold stripSchwarzExponential
  rw [Complex.exp_im,
    show (2 * (ℓ : ℂ)) = ((2 * ℓ : ℝ) : ℂ) by push_cast; rfl,
    Complex.div_ofReal_re, Complex.div_ofReal_im]
  congr 1 <;> simp [Complex.mul_re, Complex.mul_im]
end CohnElkies
