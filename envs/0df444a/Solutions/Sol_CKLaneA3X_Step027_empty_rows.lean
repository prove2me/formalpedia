-- Prove2me | solution 1 for CKLaneA3X.Step027.empty_rows
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-09-25T02:46:22.787006+00:00
-- url     : https://prove2.me/submissions/2f266e11-a6f0-4252-884d-3c1b76c92df7

import Mathlib.Data.List.GetD
import Mathlib.Data.Fintype.Fin
import Mathlib.Tactic.FinCases
import Definitions.Def_A3X_numeric_core
import Definitions.Def_A3X_Step027_data_functions

set_option maxHeartbeats 0
set_option maxRecDepth 100000
open CKLaneA3X

theorem solution (i : Fin 13) : (TPoly.mulT D_Us.P D_Us.P 24).getD (([0, 1, 3, 5, 7, 9, 11, 13, 15, 17, 19, 21, 23] : List Nat).getD i 0) [] = D_UsUs.P.getD (([0, 1, 3, 5, 7, 9, 11, 13, 15, 17, 19, 21, 23] : List Nat).getD i 0) [] := by
  fin_cases i <;> decide +kernel
