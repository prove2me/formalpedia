-- Prove2me | solution 2 for CohnElkies.saddleSourceStationaryLogRadius_eq_saddleLogRadius
-- status  : ACCEPTED   (prove)
-- author  : @fizzyinc3
-- created : 2026-10-19T12:16:51.168891+00:00
-- url     : https://prove2.me/submissions/ba8906de-8d9f-4362-9b8d-e423674ae91c

import Mathlib
import Definitions.Def_SpherePacking
set_option autoImplicit true
open CohnElkies
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
set_option maxHeartbeats 800000
noncomputable section
open Filter Set MeasureTheory intervalIntegral
open scoped Topology


theorem solution
    (ε : ℝ) (d : ℕ) (u : ℝ) :
    saddleSourceStationaryLogRadius ε ((d : ℝ) / 2) u =
      saddleLogRadius ε d u := by
  unfold saddleSourceStationaryLogRadius saddleLogRadius saddleSourceShellDerivative
  ring

