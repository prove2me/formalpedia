-- Prove2me | solution 1 for CKLaneA3X.Step027.row8
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-09-25T02:56:59.136712+00:00
-- url     : https://prove2.me/submissions/e7745949-4711-4249-b923-f0ddb5c91ee2

import Mathlib.Data.List.GetD
import Mathlib.Data.Fintype.Fin
import Mathlib.Tactic.FinCases
import Definitions.Def_A3X_numeric_core
import Definitions.Def_A3X_Step027_data_functions

set_option maxHeartbeats 0
set_option maxRecDepth 100000
open CKLaneA3X

theorem solution : (TPoly.mulT D_Us.P D_Us.P 24).getD 8 [] = D_UsUs.P.getD 8 [] := by
  decide +kernel
