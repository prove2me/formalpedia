-- Prove2me | solution 1 for BilinearGramian.Integrability.controllable
-- status  : ACCEPTED   (prove)
-- author  : @miao
-- created : 2026-10-18T09:12:04.833429+00:00
-- url     : https://prove2.me/submissions/df739bb8-54bc-4476-8120-abed77e9d2f0

import Mathlib
import Definitions.Def_BilinearGramian_Integrability_LinGramian
import Definitions.Def_BilinearGramian_Integrability_Example33

open Matrix BilinearGramian.Integrability

theorem solution : IsControllable exA exB := by
  intro v hv
  have h0 := congrFun (hv 0 (by norm_num)) 0
  have h1 := congrFun (hv 1 (by norm_num)) 0
  norm_num [exA, exB, exb, Matrix.vecMul, Matrix.mul_apply,
    dotProduct, Fin.sum_univ_two] at h0 h1
  have v0 : v 0 = 0 := by linarith
  have v1 : v 1 = 0 := by linarith
  funext i
  fin_cases i
  · exact v0
  · exact v1

#print axioms solution
