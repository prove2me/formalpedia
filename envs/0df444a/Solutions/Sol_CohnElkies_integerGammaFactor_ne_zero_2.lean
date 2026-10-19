-- Prove2me | solution 2 for CohnElkies.integerGammaFactor_ne_zero
-- status  : ACCEPTED   (prove)
-- author  : @fizzyinc3
-- created : 2026-10-19T12:08:32.945814+00:00
-- url     : https://prove2.me/submissions/78a623fc-f243-4e04-98a0-bab634dbc9bb

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


theorem solution
    (j : ℕ) {y : ℝ} (hy : y ≠ 0) :
    (j : ℂ) + Complex.I * (y : ℂ) / 2 ≠ 0 := by
  intro h
  have := congrArg Complex.im h
  simp at this
  exact hy this

