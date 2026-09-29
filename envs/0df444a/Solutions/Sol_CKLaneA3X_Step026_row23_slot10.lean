-- Prove2me | solution 1 for CKLaneA3X.Step026.row23_slot10
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-09-25T00:24:47.62554+00:00
-- url     : https://prove2.me/submissions/26a2e846-1952-4c2b-b54b-2b05193b3698

import Definitions.Def_A3X_numeric_core
import Definitions.Def_A3X_Step026_data

set_option maxRecDepth 100000
set_option maxHeartbeats 0
open CKLaneA3X

theorem solution : (((TPoly.mulT D_m.P D_inner.P 24).getD 23 []).getD 10 (0, [])).2 = ((D_mInner.P.getD 23 []).getD 10 (0, [])).2 := by
  decide +kernel
