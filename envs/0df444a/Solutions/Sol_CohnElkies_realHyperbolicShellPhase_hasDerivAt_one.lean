-- Prove2me | solution 1 for CohnElkies.realHyperbolicShellPhase_hasDerivAt_one
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-10-19T11:37:26.273981+00:00
-- url     : https://prove2.me/submissions/9719e621-8c12-4932-bd92-39a4d86761ba

import Mathlib
import Definitions.Def_SpherePacking
import Theorems.Thm_CohnElkies_realHyperbolicShellPhase_hasDerivAt

set_option autoImplicit true
open CohnElkies
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
set_option maxHeartbeats 800000
noncomputable section
open Filter MeasureTheory Set
open scoped Topology
namespace CohnElkies
theorem _root_.solution
    {ε : ℝ}
    (hε : 0 < ε)
    (horder : shortCutoff ε ≤ shortEndpoint ε) :
    HasDerivAt (realHyperbolicShellPhase ε)
      (saddleShellDerivativeOne ε) 1 := by
  simpa [saddleShellDerivativeOne] using!
    realHyperbolicShellPhase_hasDerivAt hε horder 1
end CohnElkies
