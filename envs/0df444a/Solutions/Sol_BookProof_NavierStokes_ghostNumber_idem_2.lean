-- Prove2me | solution 2 for BookProof.NavierStokes.ghostNumber_idem
-- status  : ACCEPTED   (prove)
-- author  : @Patrick
-- created : 2026-09-07T17:36:33.297522+00:00
-- url     : https://prove2.me/submissions/e1157fe3-b922-4847-a6a7-7664cc620d4b

import Definitions.Def_ChapterNavierStokes
import Mathlib.Tactic.FinCases
import Mathlib.Tactic.NormNum

open BookProof.NavierStokes Matrix

theorem solution : ghostNumber * ghostNumber = ghostNumber := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    norm_num [ghostNumber, ghostCreate, ghostAnnih, Matrix.mul_apply, Fin.sum_univ_two]

#print axioms solution
