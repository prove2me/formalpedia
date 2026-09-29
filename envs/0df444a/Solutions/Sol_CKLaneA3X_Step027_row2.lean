-- Prove2me | solution 1 for CKLaneA3X.Step027.row2
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-09-25T02:46:21.450041+00:00
-- url     : https://prove2.me/submissions/5ad19a52-20e6-4342-91ec-d36a159ddcbe

import Mathlib.Data.List.GetD
import Mathlib.Data.Fintype.Fin
import Mathlib.Tactic.FinCases
import Definitions.Def_A3X_numeric_core
import Definitions.Def_A3X_Step027_data_functions

set_option maxHeartbeats 0
set_option maxRecDepth 100000
open CKLaneA3X

theorem solution : (TPoly.mulT D_Us.P D_Us.P 24).getD 2 [] = D_UsUs.P.getD 2 [] := by
  decide +kernel
