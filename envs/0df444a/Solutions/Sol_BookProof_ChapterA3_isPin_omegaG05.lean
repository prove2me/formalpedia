-- Prove2me | solution 1 for BookProof.ChapterA3.isPin_omegaG05
-- status  : ACCEPTED   (prove)
-- author  : @miao
-- created : 2026-10-06T17:26:13.180983+00:00
-- url     : https://prove2.me/submissions/7831764c-a20f-4f1a-93e1-dab296a1192b

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

private lemma lambda_local : HasLambda omegaG05 (-minkowskiMat) := by
  intro μ
  rw [inverse_local]
  ext i j
  fin_cases μ <;> fin_cases i <;> fin_cases j <;>
    norm_num [omegaA0, omegaA5, omegaA5Z, omegaG05, omegaG05Z, mgammaR, mgammaZ, mgamma5Z, minkowskiMat, minkowskiR, minkowskiZ, Matrix.mul_apply, Fin.sum_univ_succ, Matrix.one_apply]



theorem solution : IsPin omegaG05 := by
  have hd : omegaG05.det * omegaG05.det = 1 := by
    simpa [Matrix.det_neg, show (-1 : ℝ) ^ 4 = 1 by norm_num] using congrArg Matrix.det square_local
  have hu : IsUnit omegaG05.det := isUnit_iff_ne_zero.mpr (by intro hz; simp [hz] at hd)
  have ha : |omegaG05.det| = 1 := by
    have hh : |omegaG05.det| * |omegaG05.det| = 1 := by
      simpa only [abs_mul, abs_one] using congrArg abs hd
    nlinarith [abs_nonneg omegaG05.det]
  exact ⟨hu, ha, (-minkowskiMat), lambda_local⟩

#print axioms solution
