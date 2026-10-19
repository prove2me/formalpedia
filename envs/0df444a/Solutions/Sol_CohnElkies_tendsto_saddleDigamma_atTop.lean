-- Prove2me | solution 1 for CohnElkies.tendsto_saddleDigamma_atTop
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-10-19T11:37:32.057836+00:00
-- url     : https://prove2.me/submissions/b7aba956-a4a2-4885-9fbf-0d59186d8900

import Mathlib
import Definitions.Def_SpherePacking

set_option autoImplicit true
open CohnElkies
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
set_option maxHeartbeats 800000
noncomputable section
open Filter MeasureTheory Set
open scoped Topology BigOperators
namespace CohnElkies
theorem _root_.solution :
    Tendsto saddleDigamma atTop atTop := by
  have h := Real.tendsto_log_atTop.atTop_add
    tendsto_saddleDigamma_sub_log
  convert! h using 1
  funext x
  ring
end CohnElkies
