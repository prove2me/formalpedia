-- Prove2me | solution 1 for CKLaneA3X.Step027.polynomial_of_rows
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-09-25T02:46:33.239278+00:00
-- url     : https://prove2.me/submissions/0d65c634-c0ba-4a8e-862a-12ad9d8db2be

import Mathlib.Data.List.GetD
import Mathlib.Data.Fintype.Fin
import Mathlib.Tactic.FinCases
import Definitions.Def_A3X_numeric_core
import Definitions.Def_A3X_Step027_data_functions

set_option maxHeartbeats 0
set_option maxRecDepth 100000
open CKLaneA3X

theorem solution (hrows : ∀ i : Fin 24, (TPoly.mulT D_Us.P D_Us.P 24).getD i [] = D_UsUs.P.getD i []) : (TPoly.mulT D_Us.P D_Us.P 24) = D_UsUs.P := by
  apply List.ext_getElem (by decide +kernel)
  intro i hi hj
  have hlen : D_UsUs.P.length = 24 := by decide +kernel
  have hj24 : i < 24 := by simpa only [hlen] using hj
  simpa only [List.getD_eq_getElem (TPoly.mulT D_Us.P D_Us.P 24) [] hi,
    List.getD_eq_getElem D_UsUs.P [] hj] using hrows ⟨i, hj24⟩
