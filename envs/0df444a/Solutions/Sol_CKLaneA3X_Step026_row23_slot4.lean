-- Prove2me | solution 1 for CKLaneA3X.Step026.row23_slot4
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-09-25T00:18:17.228357+00:00
-- url     : https://prove2.me/submissions/349a9932-c3d3-40f8-be79-bbda82f2bf03

import Definitions.Def_A3X_numeric_core
import Definitions.Def_A3X_Step026_data

set_option maxRecDepth 100000
set_option maxHeartbeats 0
open CKLaneA3X

theorem solution : (((TPoly.mulT D_m.P D_inner.P 24).getD 23 []).getD 4 (0, [])).2 = ((D_mInner.P.getD 23 []).getD 4 (0, [])).2 := by
  decide +kernel
