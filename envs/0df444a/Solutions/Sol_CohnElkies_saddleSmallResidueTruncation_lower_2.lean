-- Prove2me | solution 2 for CohnElkies.saddleSmallResidueTruncation_lower
-- status  : ACCEPTED   (prove)
-- author  : @fizzyinc3
-- created : 2026-10-19T12:09:57.561443+00:00
-- url     : https://prove2.me/submissions/a2be8120-a954-4884-9915-d78dbb2e4f26

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
    (ℓ : ℝ) :
    20 * Real.log ℓ ≤
      (saddleSmallResidueTruncation ℓ : ℝ) := by
  exact Nat.le_ceil _

