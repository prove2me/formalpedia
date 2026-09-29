-- Prove2me | solution 1 for CKLaneA3X.Step027.row12
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-09-25T02:46:22.128761+00:00
-- url     : https://prove2.me/submissions/42be6dd5-a14b-4f8f-83c8-aa600a1e5cbd

import Mathlib.Data.List.GetD
import Mathlib.Data.Fintype.Fin
import Mathlib.Tactic.FinCases
import Definitions.Def_A3X_numeric_core
import Definitions.Def_A3X_Step027_data_functions

set_option maxHeartbeats 0
set_option maxRecDepth 100000
open CKLaneA3X

theorem solution : (TPoly.mulT D_Us.P D_Us.P 24).getD 12 [] = D_UsUs.P.getD 12 [] := by
  decide +kernel
