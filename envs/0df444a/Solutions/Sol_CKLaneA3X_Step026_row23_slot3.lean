-- Prove2me | solution 1 for CKLaneA3X.Step026.row23_slot3
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-09-25T00:18:29.951194+00:00
-- url     : https://prove2.me/submissions/464d2a05-9604-4a8a-be02-d9aa80dd1d0b

import Definitions.Def_A3X_numeric_core
import Definitions.Def_A3X_Step026_data

set_option maxRecDepth 100000
set_option maxHeartbeats 0
open CKLaneA3X

theorem solution : (((TPoly.mulT D_m.P D_inner.P 24).getD 23 []).getD 3 (0, [])).2 = ((D_mInner.P.getD 23 []).getD 3 (0, [])).2 := by
  decide +kernel
