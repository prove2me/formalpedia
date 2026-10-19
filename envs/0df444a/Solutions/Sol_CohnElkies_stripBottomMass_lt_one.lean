-- Prove2me | solution 1 for CohnElkies.stripBottomMass_lt_one
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-10-19T11:37:21.360486+00:00
-- url     : https://prove2.me/submissions/8d7fc63b-24fb-4445-9efb-2789b1d5ee9d

import Mathlib
import Definitions.Def_SpherePacking

set_option autoImplicit true
open CohnElkies
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
set_option maxHeartbeats 800000
noncomputable section
namespace CohnElkies
theorem _root_.solution {σ : ℝ} (hσ : -1 < σ) :
    stripBottomMass σ < 1 := by
  unfold stripBottomMass
  linarith
end CohnElkies
