-- Prove2me | solution 1 for CKLaneA3X.Step026.row23_slot5
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-09-25T00:18:30.567457+00:00
-- url     : https://prove2.me/submissions/fbecfbc8-e9ab-4b86-abd0-713f2eddd4b7

import Definitions.Def_A3X_numeric_core
import Definitions.Def_A3X_Step026_data

set_option maxRecDepth 100000
set_option maxHeartbeats 0
open CKLaneA3X

theorem solution : (((TPoly.mulT D_m.P D_inner.P 24).getD 23 []).getD 5 (0, [])).2 = ((D_mInner.P.getD 23 []).getD 5 (0, [])).2 := by
  decide +kernel
