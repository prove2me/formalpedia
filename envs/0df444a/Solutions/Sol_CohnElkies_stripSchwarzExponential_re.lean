-- Prove2me | solution 1 for CohnElkies.stripSchwarzExponential_re
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-10-19T11:37:21.360486+00:00
-- url     : https://prove2.me/submissions/5c478bcc-88a0-4d9c-8c7b-4ecaca18f4cd

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
    (stripSchwarzExponential ℓ z y).re =
      Real.exp (Real.pi * (z.re - y) / (2 * ℓ)) *
        Real.cos (Real.pi * (z.im + ℓ) / (2 * ℓ)) := by
  unfold stripSchwarzExponential
  rw [Complex.exp_re,
    show (2 * (ℓ : ℂ)) = ((2 * ℓ : ℝ) : ℂ) by push_cast; rfl,
    Complex.div_ofReal_re, Complex.div_ofReal_im]
  congr 1 <;> simp [Complex.mul_re, Complex.mul_im]
end CohnElkies
