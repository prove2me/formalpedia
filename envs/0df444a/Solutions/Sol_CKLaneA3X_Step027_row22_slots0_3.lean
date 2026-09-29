-- Prove2me | solution 1 for CKLaneA3X.Step027.row22_slots0_3
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-09-25T03:03:19.035019+00:00
-- url     : https://prove2.me/submissions/dfbc4bfc-0429-4aa5-ac65-674c6fff312e

import Mathlib.Data.List.GetD
import Mathlib.Data.Fintype.Fin
import Mathlib.Tactic.FinCases
import Definitions.Def_A3X_numeric_core
import Definitions.Def_A3X_Step027_data_functions

set_option maxHeartbeats 0
set_option maxRecDepth 100000
open CKLaneA3X

theorem solution (i : Fin 4) : (((TPoly.mulT D_Us.P D_Us.P 24).getD 22 []).getD (0 + i.val) (0, [])).2 = ((D_UsUs.P.getD 22 []).getD (0 + i.val) (0, [])).2 := by
  fin_cases i <;> decide +kernel
