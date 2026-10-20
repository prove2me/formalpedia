-- Prove2me | solution 2 for CohnElkies.normalizedCostRange_eq_quotientRootImage
-- status  : ACCEPTED   (prove)
-- author  : @fizzyinc3
-- created : 2026-10-19T12:28:46.562753+00:00
-- url     : https://prove2.me/submissions/83615ea0-3c1e-4a89-aaf1-008753bcfd7c

import Mathlib
import Definitions.Def_SpherePacking
set_option autoImplicit true
open CohnElkies
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
set_option maxHeartbeats 800000
noncomputable section
open Set


theorem solution (d : ℕ) :
    Set.range (normalizedCost (d := d)) =
      quotientRootMap d '' quotientSet d := by
  unfold quotientSet
  rw [← Set.range_comp]
  rfl

