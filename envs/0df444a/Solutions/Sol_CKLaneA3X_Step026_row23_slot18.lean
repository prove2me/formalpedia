-- Prove2me | solution 1 for CKLaneA3X.Step026.row23_slot18
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-09-25T00:26:29.637258+00:00
-- url     : https://prove2.me/submissions/64d97520-79d7-48ba-9ebe-d28d804f2f68

import Definitions.Def_A3X_numeric_core
import Definitions.Def_A3X_Step026_data

set_option maxRecDepth 100000
set_option maxHeartbeats 0
open CKLaneA3X

theorem solution : (((TPoly.mulT D_m.P D_inner.P 24).getD 23 []).getD 18 (0, [])).2 = ((D_mInner.P.getD 23 []).getD 18 (0, [])).2 := by
  decide +kernel
