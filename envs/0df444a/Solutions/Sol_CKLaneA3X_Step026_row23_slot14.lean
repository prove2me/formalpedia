-- Prove2me | solution 1 for CKLaneA3X.Step026.row23_slot14
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-09-25T00:26:17.578894+00:00
-- url     : https://prove2.me/submissions/250727f5-d3b7-4a12-920e-d03a15f06851

import Definitions.Def_A3X_numeric_core
import Definitions.Def_A3X_Step026_data

set_option maxRecDepth 100000
set_option maxHeartbeats 0
open CKLaneA3X

theorem solution : (((TPoly.mulT D_m.P D_inner.P 24).getD 23 []).getD 14 (0, [])).2 = ((D_mInner.P.getD 23 []).getD 14 (0, [])).2 := by
  decide +kernel
