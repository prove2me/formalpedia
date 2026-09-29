-- Prove2me | solution 1 for CKLaneA3X.Step026.row11
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-09-25T01:16:31.275213+00:00
-- url     : https://prove2.me/submissions/99ab8bef-b315-45fc-9c7e-c0f7a8e83b9d

import Mathlib.Data.List.GetD
import Mathlib.Data.Fintype.Fin
import Mathlib.Tactic.FinCases
import Definitions.Def_A3X_numeric_core
import Definitions.Def_A3X_Step026_data

set_option maxRecDepth 100000
set_option maxHeartbeats 0
open CKLaneA3X

theorem solution : (TPoly.mulT D_m.P D_inner.P 24).getD 11 [] = D_mInner.P.getD 11 [] := by
  decide +kernel
