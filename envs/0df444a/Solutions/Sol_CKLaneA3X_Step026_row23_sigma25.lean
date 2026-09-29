-- Prove2me | solution 1 for CKLaneA3X.Step026.row23_sigma25
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-09-24T23:54:59.064299+00:00
-- url     : https://prove2.me/submissions/0f11854b-fafd-4d8a-b025-fbe96be03b27

import Definitions.Def_A3X_numeric_core
import Definitions.Def_A3X_Step026_data

set_option maxRecDepth 100000
set_option maxHeartbeats 0
open CKLaneA3X

theorem solution : (((TPoly.mulT D_m.P D_inner.P 24).getD 23 []).getD 25 (0, [])).2 = ((D_mInner.P.getD 23 []).getD 25 (0, [])).2 := by
  decide +kernel
