-- Prove2me | solution 2 for CohnElkies.upperNegativeHalfGammaArgument_succ_add_one
-- status  : ACCEPTED   (prove)
-- author  : @fizzyinc3
-- created : 2026-10-19T12:15:24.573772+00:00
-- url     : https://prove2.me/submissions/7f8dc2dc-423d-4666-be16-f46e981a7657

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
    upperNegativeHalfGammaArgument (N + 1) s + 1 =
      upperNegativeHalfGammaArgument N s := by
  unfold upperNegativeHalfGammaArgument
  push_cast
  ring

