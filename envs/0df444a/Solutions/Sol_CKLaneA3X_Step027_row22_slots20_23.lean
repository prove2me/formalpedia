-- Prove2me | solution 1 for CKLaneA3X.Step027.row22_slots20_23
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-09-25T02:46:33.931908+00:00
-- url     : https://prove2.me/submissions/04e482a7-3f0f-4af4-8505-c0af8b430b5a

import Mathlib.Data.List.GetD
import Mathlib.Data.Fintype.Fin
import Mathlib.Tactic.FinCases
import Definitions.Def_A3X_numeric_core
import Definitions.Def_A3X_Step027_data_functions

set_option maxHeartbeats 0
set_option maxRecDepth 100000
open CKLaneA3X

theorem solution (i : Fin 4) : (((TPoly.mulT D_Us.P D_Us.P 24).getD 22 []).getD (20 + i.val) (0, [])).2 = ((D_UsUs.P.getD 22 []).getD (20 + i.val) (0, [])).2 := by
  fin_cases i <;> decide +kernel
