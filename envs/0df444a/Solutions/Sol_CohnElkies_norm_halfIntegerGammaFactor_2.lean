-- Prove2me | solution 2 for CohnElkies.norm_halfIntegerGammaFactor
-- status  : ACCEPTED   (prove)
-- author  : @fizzyinc3
-- created : 2026-10-19T12:22:30.843+00:00
-- url     : https://prove2.me/submissions/5328ed7d-f345-4887-80c6-bee390e67474

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
    ‖(j : ℂ) + (1 / 2 : ℂ) + Complex.I * (y : ℂ) / 2‖ =
      Real.sqrt (((j : ℝ) + 1 / 2) ^ 2 + (y / 2) ^ 2) := by
  rw [Complex.norm_def, Complex.normSq_apply]
  congr 1
  simp
  ring

