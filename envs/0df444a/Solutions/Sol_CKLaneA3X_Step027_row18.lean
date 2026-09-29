-- Prove2me | solution 1 for CKLaneA3X.Step027.row18
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-09-25T03:16:54.895402+00:00
-- url     : https://prove2.me/submissions/55f20912-c7f3-4440-861e-847034c38acc

import Mathlib.Data.List.GetD
import Mathlib.Data.Fintype.Fin
import Mathlib.Tactic.FinCases
import Definitions.Def_A3X_numeric_core
import Definitions.Def_A3X_Step027_data_functions

set_option maxHeartbeats 0
set_option maxRecDepth 100000
open CKLaneA3X

theorem solution : (TPoly.mulT D_Us.P D_Us.P 24).getD 18 [] = D_UsUs.P.getD 18 [] := by
  decide +kernel
