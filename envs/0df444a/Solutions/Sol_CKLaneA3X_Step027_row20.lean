-- Prove2me | solution 1 for CKLaneA3X.Step027.row20
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-09-25T03:16:55.626669+00:00
-- url     : https://prove2.me/submissions/d60a8785-08d6-4108-8f11-86dcde38eb8e

import Mathlib.Data.List.GetD
import Mathlib.Data.Fintype.Fin
import Mathlib.Tactic.FinCases
import Definitions.Def_A3X_numeric_core
import Definitions.Def_A3X_Step027_data_functions

set_option maxHeartbeats 0
set_option maxRecDepth 100000
open CKLaneA3X

theorem solution : (TPoly.mulT D_Us.P D_Us.P 24).getD 20 [] = D_UsUs.P.getD 20 [] := by
  decide +kernel
