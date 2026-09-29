-- Prove2me | solution 1 for CKLaneA3X.Step027.row10
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-09-25T02:56:38.714626+00:00
-- url     : https://prove2.me/submissions/bf935908-75fd-4016-87a9-11650a8b3b24

import Mathlib.Data.List.GetD
import Mathlib.Data.Fintype.Fin
import Mathlib.Tactic.FinCases
import Definitions.Def_A3X_numeric_core
import Definitions.Def_A3X_Step027_data_functions

set_option maxHeartbeats 0
set_option maxRecDepth 100000
open CKLaneA3X

theorem solution : (TPoly.mulT D_Us.P D_Us.P 24).getD 10 [] = D_UsUs.P.getD 10 [] := by
  decide +kernel
