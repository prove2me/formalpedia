-- Prove2me | solution 1 for CKLaneA3X.Step027.row22_slots24_24
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-09-25T03:03:08.926421+00:00
-- url     : https://prove2.me/submissions/99280ebd-e544-4f56-9299-0cf22555bd10

import Mathlib.Data.List.GetD
import Mathlib.Data.Fintype.Fin
import Mathlib.Tactic.FinCases
import Definitions.Def_A3X_numeric_core
import Definitions.Def_A3X_Step027_data_functions

set_option maxHeartbeats 0
set_option maxRecDepth 100000
open CKLaneA3X

theorem solution : (((TPoly.mulT D_Us.P D_Us.P 24).getD 22 []).getD 24 (0, [])).2 = ((D_UsUs.P.getD 22 []).getD 24 (0, [])).2 := by
  decide +kernel
