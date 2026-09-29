-- Prove2me | solution 1 for CKLaneA3X.Step027.row6
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-09-25T02:56:49.012277+00:00
-- url     : https://prove2.me/submissions/d0989645-c65c-422d-873e-6e0dae372a2f

import Mathlib.Data.List.GetD
import Mathlib.Data.Fintype.Fin
import Mathlib.Tactic.FinCases
import Definitions.Def_A3X_numeric_core
import Definitions.Def_A3X_Step027_data_functions

set_option maxHeartbeats 0
set_option maxRecDepth 100000
open CKLaneA3X

theorem solution : (TPoly.mulT D_Us.P D_Us.P 24).getD 6 [] = D_UsUs.P.getD 6 [] := by
  decide +kernel
