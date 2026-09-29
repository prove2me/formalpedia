-- Prove2me | solution 1 for CKLaneA3X.Step026.empty_rows
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-09-25T00:57:24.619069+00:00
-- url     : https://prove2.me/submissions/3c7e4ca8-cc53-4976-a7ed-0e098fea29ad

import Mathlib.Data.List.GetD
import Mathlib.Data.Fintype.Fin
import Mathlib.Tactic.FinCases
import Definitions.Def_A3X_numeric_core
import Definitions.Def_A3X_Step026_data

set_option maxRecDepth 100000
set_option maxHeartbeats 0
open CKLaneA3X

theorem solution (i : Fin 13) : (TPoly.mulT D_m.P D_inner.P 24).getD (([0, 1, 2, 4, 6, 8, 10, 12, 14, 16, 18, 20, 22] : List Nat).getD i 0) [] = D_mInner.P.getD (([0, 1, 2, 4, 6, 8, 10, 12, 14, 16, 18, 20, 22] : List Nat).getD i 0) [] := by
  fin_cases i <;> decide +kernel
