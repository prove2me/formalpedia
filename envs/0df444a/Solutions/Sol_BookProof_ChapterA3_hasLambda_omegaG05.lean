-- Prove2me | solution 1 for BookProof.ChapterA3.hasLambda_omegaG05
-- status  : ACCEPTED   (prove)
-- author  : @miao
-- created : 2026-10-06T17:23:18.923986+00:00
-- url     : https://prove2.me/submissions/b89cdf95-fdaf-44b2-a003-336eae8cd29c

import Mathlib
import Definitions.Def_ChapterA3d
open BookProof.ChapterA3 Matrix
set_option autoImplicit false
set_option maxHeartbeats 0

private lemma square_local : omegaG05 * omegaG05 = -1 := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    norm_num [omegaA0, omegaA5, omegaA5Z, omegaG05, omegaG05Z, mgammaR, mgammaZ, mgamma5Z, Matrix.mul_apply, Fin.sum_univ_succ]

private lemma inverse_local : omegaG05⁻¹ = -omegaG05 := by
  apply Matrix.inv_eq_left_inv
  rw [neg_mul, square_local, neg_neg]

theorem solution : HasLambda omegaG05 (-minkowskiMat) := by
  intro μ
  rw [inverse_local]
  ext i j
  fin_cases μ <;> fin_cases i <;> fin_cases j <;>
    norm_num [omegaA0, omegaA5, omegaA5Z, omegaG05, omegaG05Z, mgammaR, mgammaZ, mgamma5Z, minkowskiMat, minkowskiR, minkowskiZ, Matrix.mul_apply, Fin.sum_univ_succ, Matrix.one_apply]

#print axioms solution
