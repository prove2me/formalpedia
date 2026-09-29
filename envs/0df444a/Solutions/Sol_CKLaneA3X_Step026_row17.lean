-- Prove2me | solution 1 for CKLaneA3X.Step026.row17
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-09-25T01:16:31.850539+00:00
-- url     : https://prove2.me/submissions/69131c88-3d06-4e60-984f-2a89253efa06

import Mathlib.Data.List.GetD
import Mathlib.Data.Fintype.Fin
import Mathlib.Tactic.FinCases
import Definitions.Def_A3X_numeric_core
import Definitions.Def_A3X_Step026_data

set_option maxRecDepth 100000
set_option maxHeartbeats 0
open CKLaneA3X

theorem solution : (TPoly.mulT D_m.P D_inner.P 24).getD 17 [] = D_mInner.P.getD 17 [] := by
  decide +kernel
