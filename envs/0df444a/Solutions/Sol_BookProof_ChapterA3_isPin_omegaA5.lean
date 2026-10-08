-- Prove2me | solution 1 for BookProof.ChapterA3.isPin_omegaA5
-- status  : ACCEPTED   (prove)
-- author  : @miao
-- created : 2026-10-06T17:25:23.959297+00:00
-- url     : https://prove2.me/submissions/ec9e9e8e-9580-42b7-9274-fcb7a4034a20

import Mathlib
import Definitions.Def_ChapterA3d
open BookProof.ChapterA3 Matrix
set_option autoImplicit false
set_option maxHeartbeats 0

private lemma square_local : omegaA5 * omegaA5 = -1 := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    norm_num [omegaA0, omegaA5, omegaA5Z, omegaG05, omegaG05Z, mgammaR, mgammaZ, mgamma5Z, Matrix.mul_apply, Fin.sum_univ_succ]

private lemma inverse_local : omegaA5⁻¹ = -omegaA5 := by
  apply Matrix.inv_eq_left_inv
  rw [neg_mul, square_local, neg_neg]

private lemma lambda_local : HasLambda omegaA5 (-1) := by
  intro μ
  rw [inverse_local]
  ext i j
  fin_cases μ <;> fin_cases i <;> fin_cases j <;>
    norm_num [omegaA0, omegaA5, omegaA5Z, omegaG05, omegaG05Z, mgammaR, mgammaZ, mgamma5Z, minkowskiMat, minkowskiR, minkowskiZ, Matrix.mul_apply, Fin.sum_univ_succ, Matrix.one_apply]



theorem solution : IsPin omegaA5 := by
  have hd : omegaA5.det * omegaA5.det = 1 := by
    simpa [Matrix.det_neg, show (-1 : ℝ) ^ 4 = 1 by norm_num] using congrArg Matrix.det square_local
  have hu : IsUnit omegaA5.det := isUnit_iff_ne_zero.mpr (by intro hz; simp [hz] at hd)
  have ha : |omegaA5.det| = 1 := by
    have hh : |omegaA5.det| * |omegaA5.det| = 1 := by
      simpa only [abs_mul, abs_one] using congrArg abs hd
    nlinarith [abs_nonneg omegaA5.det]
  exact ⟨hu, ha, (-1), lambda_local⟩

#print axioms solution
