-- Prove2me | solution 2 for CohnElkies.saddleTaylorContour_gammaArgument
-- status  : ACCEPTED   (prove)
-- author  : @fizzyinc3
-- created : 2026-10-19T12:18:09.466395+00:00
-- url     : https://prove2.me/submissions/4644a7fa-0d0c-4d67-839f-64beb295a315

import Mathlib
import Definitions.Def_SpherePacking
set_option autoImplicit true
open CohnElkies
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
set_option maxHeartbeats 800000
noncomputable section
open Filter MeasureTheory Set
open scoped Topology BigOperators


theorem solution
    (N : ℕ) (s : ℝ) :
    (((saddleTaylorContour N : ℂ) +
      (s : ℂ) * Complex.I) / 2) =
      upperNegativeHalfGammaArgument N (-s) := by
  apply Complex.ext <;> simp [saddleTaylorContour, upperNegativeHalfGammaArgument] <;> ring

