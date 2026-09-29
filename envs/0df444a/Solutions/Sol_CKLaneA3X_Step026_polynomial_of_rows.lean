-- Prove2me | solution 1 for CKLaneA3X.Step026.polynomial_of_rows
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-09-25T01:10:10.699452+00:00
-- url     : https://prove2.me/submissions/1db376a4-6d36-464b-8248-7778bed5d7f3

import Mathlib.Data.List.GetD
import Mathlib.Data.Fintype.Fin
import Mathlib.Tactic.FinCases
import Definitions.Def_A3X_numeric_core
import Definitions.Def_A3X_Step026_data

set_option maxRecDepth 100000
set_option maxHeartbeats 0
open CKLaneA3X

theorem solution (hrows : ∀ i : Fin 24, (TPoly.mulT D_m.P D_inner.P 24).getD i [] = D_mInner.P.getD i []) : (TPoly.mulT D_m.P D_inner.P 24) = D_mInner.P := by
  apply List.ext_getElem (by decide +kernel)
  intro i hi hj
  have hlen : D_mInner.P.length = 24 := by decide +kernel
  have hj24 : i < 24 := by simpa only [hlen] using hj
  simpa only [List.getD_eq_getElem (TPoly.mulT D_m.P D_inner.P 24) [] hi,
    List.getD_eq_getElem D_mInner.P [] hj] using hrows ⟨i, hj24⟩
