-- Prove2me | solution 1 for CKLaneA3X.Step026.row9
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-09-25T01:16:20.673154+00:00
-- url     : https://prove2.me/submissions/e058cc4f-fc09-4dd9-994b-2f74acbc99ec

import Mathlib.Data.List.GetD
import Mathlib.Data.Fintype.Fin
import Mathlib.Tactic.FinCases
import Definitions.Def_A3X_numeric_core
import Definitions.Def_A3X_Step026_data

set_option maxRecDepth 100000
set_option maxHeartbeats 0
open CKLaneA3X

theorem solution : (TPoly.mulT D_m.P D_inner.P 24).getD 9 [] = D_mInner.P.getD 9 [] := by
  decide +kernel
