-- Prove2me | solution 2 for CohnElkies.norm_integerGammaFactor
-- status  : ACCEPTED   (prove)
-- author  : @fizzyinc3
-- created : 2026-10-19T12:06:28.738886+00:00
-- url     : https://prove2.me/submissions/c49bc2d5-d770-4a47-b418-d7b295ab4aef

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


theorem solution (j : ℕ) (y : ℝ) :
    ‖(j : ℂ) + Complex.I * (y : ℂ) / 2‖ =
      Real.sqrt ((j : ℝ) ^ 2 + (y / 2) ^ 2) := by
  rw [show (j : ℂ) + Complex.I * (y : ℂ) / 2 = ((j:ℝ):ℂ) + ((y/2:ℝ):ℂ) * Complex.I by push_cast; ring]
  exact Complex.norm_add_mul_I _ _

