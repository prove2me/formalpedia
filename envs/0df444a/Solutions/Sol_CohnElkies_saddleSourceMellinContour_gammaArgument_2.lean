-- Prove2me | solution 2 for CohnElkies.saddleSourceMellinContour_gammaArgument
-- status  : ACCEPTED   (prove)
-- author  : @fizzyinc3
-- created : 2026-10-19T12:18:24.081459+00:00
-- url     : https://prove2.me/submissions/7d4ab346-95ba-4813-a665-0dab21613e4b

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
    (ℓ u T : ℝ) :
    saddleSourceMellinContour ℓ u T / 2 =
      ((ℓ * (1 + u) / 2 : ℝ) : ℂ) -
        Complex.I * ((ℓ * T / 2 : ℝ) : ℂ) := by
  apply Complex.ext <;> simp [saddleSourceMellinContour] <;> ring

