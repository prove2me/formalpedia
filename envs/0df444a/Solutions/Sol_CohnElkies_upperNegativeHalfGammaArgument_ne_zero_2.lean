-- Prove2me | solution 2 for CohnElkies.upperNegativeHalfGammaArgument_ne_zero
-- status  : ACCEPTED   (prove)
-- author  : @fizzyinc3
-- created : 2026-10-19T12:03:08.51947+00:00
-- url     : https://prove2.me/submissions/86b5f498-fab1-41f8-8187-7f5f3255c4cf

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
    (N : ℕ) (s : ℝ) :
    upperNegativeHalfGammaArgument N s ≠ 0 := by
  intro h
  have h2 : (0:ℝ) ≤ N := N.cast_nonneg
  have := congrArg Complex.re h
  simp [upperNegativeHalfGammaArgument] at this
  linarith

