-- Prove2me | solution 1 for CKLaneA3X.Step026.row19_slots18_19
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-09-25T01:21:47.83521+00:00
-- url     : https://prove2.me/submissions/53e659ae-0852-4dfb-a1ff-0f334b6ca842

import Mathlib.Data.List.GetD
import Mathlib.Data.Fintype.Fin
import Mathlib.Tactic.FinCases
import Definitions.Def_A3X_numeric_core
import Definitions.Def_A3X_Step026_data

set_option maxRecDepth 100000
set_option maxHeartbeats 0
open CKLaneA3X

theorem solution (i : Fin 2) : (((TPoly.mulT D_m.P D_inner.P 24).getD 19 []).getD (18 + i.val) (0, [])).2 = ((D_mInner.P.getD 19 []).getD (18 + i.val) (0, [])).2 := by
  fin_cases i <;> decide +kernel
