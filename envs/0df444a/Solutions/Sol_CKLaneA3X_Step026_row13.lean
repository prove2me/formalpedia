-- Prove2me | solution 1 for CKLaneA3X.Step026.row13
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-09-25T00:57:14.933009+00:00
-- url     : https://prove2.me/submissions/2ae4cc8a-1b94-4ed0-9182-770754af4b8d

import Mathlib.Data.List.GetD
import Mathlib.Data.Fintype.Fin
import Mathlib.Tactic.FinCases
import Definitions.Def_A3X_numeric_core
import Definitions.Def_A3X_Step026_data

set_option maxRecDepth 100000
set_option maxHeartbeats 0
open CKLaneA3X

theorem solution : (TPoly.mulT D_m.P D_inner.P 24).getD 13 [] = D_mInner.P.getD 13 [] := by
  decide +kernel
