-- Prove2me | solution 1 for BookProof.ChapterA3.isPin_omegaA0
-- status  : ACCEPTED   (prove)
-- author  : @miao
-- created : 2026-10-06T17:24:36.364074+00:00
-- url     : https://prove2.me/submissions/ff7ca4fe-56ae-4c90-ad42-6d00e53eac43

import Mathlib
import Definitions.Def_ChapterA3d
open BookProof.ChapterA3 Matrix
set_option autoImplicit false
set_option maxHeartbeats 0

private lemma square_local : omegaA0 * omegaA0 = -1 := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    norm_num [omegaA0, omegaA5, omegaA5Z, omegaG05, omegaG05Z, mgammaR, mgammaZ, mgamma5Z, Matrix.mul_apply, Fin.sum_univ_succ]

private lemma inverse_local : omegaA0⁻¹ = -omegaA0 := by
  apply Matrix.inv_eq_left_inv
  rw [neg_mul, square_local, neg_neg]

private lemma lambda_local : HasLambda omegaA0 minkowskiMat := by
  intro μ
  rw [inverse_local]
  ext i j
  fin_cases μ <;> fin_cases i <;> fin_cases j <;>
    norm_num [omegaA0, omegaA5, omegaA5Z, omegaG05, omegaG05Z, mgammaR, mgammaZ, mgamma5Z, minkowskiMat, minkowskiR, minkowskiZ, Matrix.mul_apply, Fin.sum_univ_succ, Matrix.one_apply]



theorem solution : IsPin omegaA0 := by
  have hd : omegaA0.det * omegaA0.det = 1 := by
    simpa [Matrix.det_neg, show (-1 : ℝ) ^ 4 = 1 by norm_num] using congrArg Matrix.det square_local
  have hu : IsUnit omegaA0.det := isUnit_iff_ne_zero.mpr (by intro hz; simp [hz] at hd)
  have ha : |omegaA0.det| = 1 := by
    have hh : |omegaA0.det| * |omegaA0.det| = 1 := by
      simpa only [abs_mul, abs_one] using congrArg abs hd
    nlinarith [abs_nonneg omegaA0.det]
  exact ⟨hu, ha, minkowskiMat, lambda_local⟩

#print axioms solution
