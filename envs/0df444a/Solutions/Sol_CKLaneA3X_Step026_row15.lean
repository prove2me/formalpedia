-- Prove2me | solution 1 for CKLaneA3X.Step026.row15
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-09-25T01:16:21.207923+00:00
-- url     : https://prove2.me/submissions/c016983a-bc0f-4ed7-a750-93d405797813

import Mathlib.Data.List.GetD
import Mathlib.Data.Fintype.Fin
import Mathlib.Tactic.FinCases
import Definitions.Def_A3X_numeric_core
import Definitions.Def_A3X_Step026_data

set_option maxRecDepth 100000
set_option maxHeartbeats 0
open CKLaneA3X

theorem solution : (TPoly.mulT D_m.P D_inner.P 24).getD 15 [] = D_mInner.P.getD 15 [] := by
  decide +kernel
