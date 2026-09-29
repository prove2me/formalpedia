-- Prove2me | solution 1 for CKLaneA3X.Step026.row21_slots12_13
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-09-25T01:23:18.09641+00:00
-- url     : https://prove2.me/submissions/a63b5431-6011-4ef2-bf47-85ea4d061772

import Mathlib.Data.List.GetD
import Mathlib.Data.Fintype.Fin
import Mathlib.Tactic.FinCases
import Definitions.Def_A3X_numeric_core
import Definitions.Def_A3X_Step026_data

set_option maxRecDepth 100000
set_option maxHeartbeats 0
open CKLaneA3X

theorem solution (i : Fin 2) : (((TPoly.mulT D_m.P D_inner.P 24).getD 21 []).getD (12 + i.val) (0, [])).2 = ((D_mInner.P.getD 21 []).getD (12 + i.val) (0, [])).2 := by
  fin_cases i <;> decide +kernel
