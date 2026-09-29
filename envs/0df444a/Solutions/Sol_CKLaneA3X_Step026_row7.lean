-- Prove2me | solution 1 for CKLaneA3X.Step026.row7
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-09-25T01:16:20.022751+00:00
-- url     : https://prove2.me/submissions/f9217e1e-b535-4548-83f9-5b39b2f92ea7

import Mathlib.Data.List.GetD
import Mathlib.Data.Fintype.Fin
import Mathlib.Tactic.FinCases
import Definitions.Def_A3X_numeric_core
import Definitions.Def_A3X_Step026_data

set_option maxRecDepth 100000
set_option maxHeartbeats 0
open CKLaneA3X

theorem solution : (TPoly.mulT D_m.P D_inner.P 24).getD 7 [] = D_mInner.P.getD 7 [] := by
  decide +kernel
