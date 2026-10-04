-- Prove2me | solution 2 for BookProof.NavierStokes.ghostNumber_resolution
-- status  : ACCEPTED   (prove)
-- author  : @Patrick
-- created : 2026-09-07T17:36:34.441169+00:00
-- url     : https://prove2.me/submissions/f47445f6-d3cf-4b6f-b4cb-e766080b3c80

import Definitions.Def_ChapterNavierStokes
import Mathlib.Tactic.FinCases
import Mathlib.Tactic.NormNum

open BookProof.NavierStokes Matrix

theorem solution : ghostNumber + ghostAnnih * ghostCreate = 1 := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    norm_num [ghostNumber, ghostCreate, ghostAnnih, Matrix.mul_apply,
      Matrix.vecMul_apply_eq_sum, Fin.sum_univ_two]

#print axioms solution
