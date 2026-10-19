-- Prove2me | solution 2 for CohnElkies.continuous_quotientRootMap
-- status  : ACCEPTED   (prove)
-- author  : @fizzyinc3
-- created : 2026-10-19T12:19:48.022244+00:00
-- url     : https://prove2.me/submissions/5c03054f-860e-4208-9293-76796a80f780

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
    Continuous (quotientRootMap d) := by
  unfold quotientRootMap
  exact (Real.continuous_rpow_const (by positivity)).div_const _

