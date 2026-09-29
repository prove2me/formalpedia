-- Prove2me | solution 1 for CKLaneA3X.Step026.row23_slot2
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-09-25T00:18:29.139242+00:00
-- url     : https://prove2.me/submissions/6ad20f45-ec34-4704-8514-b650cd7c06a0

import Definitions.Def_A3X_numeric_core
import Definitions.Def_A3X_Step026_data

set_option maxRecDepth 100000
set_option maxHeartbeats 0
open CKLaneA3X

theorem solution : (((TPoly.mulT D_m.P D_inner.P 24).getD 23 []).getD 2 (0, [])).2 = ((D_mInner.P.getD 23 []).getD 2 (0, [])).2 := by
  decide +kernel
