-- Prove2me | solution 1 for CKLaneA3X.Step026.row3
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-09-25T00:57:14.322816+00:00
-- url     : https://prove2.me/submissions/b3650d51-074e-44dc-8699-857226e136fe

import Mathlib.Data.List.GetD
import Mathlib.Data.Fintype.Fin
import Mathlib.Tactic.FinCases
import Definitions.Def_A3X_numeric_core
import Definitions.Def_A3X_Step026_data

set_option maxRecDepth 100000
set_option maxHeartbeats 0
open CKLaneA3X

theorem solution : (TPoly.mulT D_m.P D_inner.P 24).getD 3 [] = D_mInner.P.getD 3 [] := by
  decide +kernel
