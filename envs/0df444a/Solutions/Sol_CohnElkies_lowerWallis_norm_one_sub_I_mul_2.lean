-- Prove2me | solution 2 for CohnElkies.lowerWallis_norm_one_sub_I_mul
-- status  : ACCEPTED   (prove)
-- author  : @fizzyinc3
-- created : 2026-10-19T11:55:56.280196+00:00
-- url     : https://prove2.me/submissions/4bb3ff00-82cd-4db5-87af-af4584b8df39

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


theorem solution (u : ℝ) :
    ‖1 - Complex.I * (u : ℂ)‖ =
      Real.sqrt (1 + u ^ 2) := by
  rw [Complex.norm_def, Complex.normSq_apply]
  congr 1
  simp; ring

