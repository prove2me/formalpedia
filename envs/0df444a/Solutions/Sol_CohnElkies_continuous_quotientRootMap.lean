-- Prove2me | solution 1 for CohnElkies.continuous_quotientRootMap
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-10-19T11:37:34.337066+00:00
-- url     : https://prove2.me/submissions/dcccb9ae-3021-4779-9f66-e6f4523ccd64

import Mathlib
import Definitions.Def_SpherePacking

set_option autoImplicit true
open CohnElkies
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
set_option maxHeartbeats 800000
noncomputable section
open Set
namespace CohnElkies
theorem _root_.solution (d : ℕ) :
    Continuous (quotientRootMap d) := by
  unfold quotientRootMap
  exact (Real.continuous_rpow_const (by positivity)).div_const _
end CohnElkies
