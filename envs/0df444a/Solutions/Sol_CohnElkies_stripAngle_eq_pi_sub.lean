-- Prove2me | solution 1 for CohnElkies.stripAngle_eq_pi_sub
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-10-19T11:37:24.652437+00:00
-- url     : https://prove2.me/submissions/6b10676f-6467-4211-ba75-a43cf97b458a

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
namespace CohnElkies
theorem _root_.solution (σ : ℝ) :
    stripAngle σ =
      Real.pi - Real.pi * (1 - σ) / 2 := by
  unfold stripAngle
  ring
end CohnElkies
