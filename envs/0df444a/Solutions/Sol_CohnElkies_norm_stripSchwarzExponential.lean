-- Prove2me | solution 1 for CohnElkies.norm_stripSchwarzExponential
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-10-19T11:37:21.360486+00:00
-- url     : https://prove2.me/submissions/7ad8e9c8-8dfc-4bea-bdd6-6677802dda0f

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
    ‖stripSchwarzExponential ℓ z y‖ =
      Real.exp (Real.pi * (z.re - y) / (2 * ℓ)) := by
  unfold stripSchwarzExponential
  rw [Complex.norm_exp,
    show (2 * (ℓ : ℂ)) = ((2 * ℓ : ℝ) : ℂ) by push_cast; rfl,
    Complex.div_ofReal_re]
  congr 1
  simp [Complex.mul_re]
end CohnElkies
