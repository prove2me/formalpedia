-- Prove2me | solution 1 for CohnElkies.stripBottomMass_pos
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-10-19T11:37:21.360486+00:00
-- url     : https://prove2.me/submissions/0ae84af4-91e6-4801-a873-6d9994e7644a

import Mathlib
import Definitions.Def_SpherePacking

set_option autoImplicit true
open CohnElkies
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
set_option maxHeartbeats 800000
noncomputable section
namespace CohnElkies
theorem _root_.solution {σ : ℝ} (hσ : σ < 1) :
    0 < stripBottomMass σ := by
  unfold stripBottomMass
  linarith
end CohnElkies
