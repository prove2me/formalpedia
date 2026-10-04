-- Prove2me | solution 2 for BookProof.NavierStokes.ghostAnticomm_create
-- status  : ACCEPTED   (prove)
-- author  : @Patrick
-- created : 2026-09-07T17:36:35.397985+00:00
-- url     : https://prove2.me/submissions/0ae7310c-fdac-432c-9acb-9483d121ff34

import Definitions.Def_ChapterNavierStokes
import Mathlib.Tactic.FinCases
import Mathlib.Tactic.NormNum

open BookProof.NavierStokes Matrix

theorem solution : ghostCreate * ghostCreate + ghostCreate * ghostCreate = 0 := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    norm_num [ghostCreate, ghostAnnih, Matrix.mul_apply, Fin.sum_univ_two]

#print axioms solution
#print axioms ghostAnnih
#print axioms ghostCreate
#print axioms ghostNumber
