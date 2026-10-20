-- Prove2me | solution 2 for CohnElkies.lowerWallisComplexLogPhase_ofReal
-- status  : ACCEPTED   (prove)
-- author  : @fizzyinc3
-- created : 2026-10-19T12:27:19.226795+00:00
-- url     : https://prove2.me/submissions/ff58628d-2d0a-4902-acda-1ebfe657c3ec

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


theorem solution
    {a : ℝ} (ha : 0 ≤ a) :
    lowerWallisComplexLogPhase (a : ℂ) =
      1 + a * Real.log a -
        (a + 1) * Real.log (a + 1) := by
  unfold lowerWallisComplexLogPhase
  have h1 : ((a:ℂ) + 1) = ((a + 1 : ℝ) : ℂ) := by push_cast; ring
  rw [h1, ← Complex.ofReal_log ha, ← Complex.ofReal_log (by linarith)]
  have h2 : (1 + (a:ℂ) * ((Real.log a : ℝ) : ℂ) - ((a+1 : ℝ) : ℂ) * ((Real.log (a+1) : ℝ) : ℂ)) =
      ((1 + a * Real.log a - (a+1) * Real.log (a+1) : ℝ) : ℂ) := by push_cast; ring
  rw [h2, Complex.ofReal_re]

