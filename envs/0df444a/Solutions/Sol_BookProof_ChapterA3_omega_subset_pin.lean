-- Prove2me | solution 1 for BookProof.ChapterA3.omega_subset_pin
-- status  : ACCEPTED   (prove)
-- author  : @miao
-- created : 2026-10-06T17:29:11.486997+00:00
-- url     : https://prove2.me/submissions/9ad1bd39-2ad8-43f3-b39b-ea1bb0cd5e1c

import Mathlib
import Definitions.Def_ChapterA3d
open BookProof.ChapterA3 Matrix
set_option autoImplicit false
set_option maxHeartbeats 0

private lemma square_omegaA0 : omegaA0 * omegaA0 = -1 := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    norm_num [omegaA0, omegaA5, omegaA5Z, omegaG05, omegaG05Z, mgammaR, mgammaZ, mgamma5Z, Matrix.mul_apply, Fin.sum_univ_succ]

private lemma inverse_omegaA0 : omegaA0⁻¹ = -omegaA0 := by
  apply Matrix.inv_eq_left_inv
  rw [neg_mul, square_omegaA0, neg_neg]

private lemma lambda_omegaA0 : HasLambda omegaA0 minkowskiMat := by
  intro μ
  rw [inverse_omegaA0]
  ext i j
  fin_cases μ <;> fin_cases i <;> fin_cases j <;>
    norm_num [omegaA0, omegaA5, omegaA5Z, omegaG05, omegaG05Z, mgammaR, mgammaZ, mgamma5Z, minkowskiMat, minkowskiR, minkowskiZ, Matrix.mul_apply, Fin.sum_univ_succ, Matrix.one_apply]



private lemma pin_omegaA0 : IsPin omegaA0 := by
  have hd : omegaA0.det * omegaA0.det = 1 := by
    simpa [Matrix.det_neg, show (-1 : ℝ) ^ 4 = 1 by norm_num] using congrArg Matrix.det square_omegaA0
  have hu : IsUnit omegaA0.det := isUnit_iff_ne_zero.mpr (by intro hz; simp [hz] at hd)
  have ha : |omegaA0.det| = 1 := by
    have hh : |omegaA0.det| * |omegaA0.det| = 1 := by
      simpa only [abs_mul, abs_one] using congrArg abs hd
    nlinarith [abs_nonneg omegaA0.det]
  exact ⟨hu, ha, minkowskiMat, lambda_omegaA0⟩



private lemma square_omegaA5 : omegaA5 * omegaA5 = -1 := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    norm_num [omegaA0, omegaA5, omegaA5Z, omegaG05, omegaG05Z, mgammaR, mgammaZ, mgamma5Z, Matrix.mul_apply, Fin.sum_univ_succ]

private lemma inverse_omegaA5 : omegaA5⁻¹ = -omegaA5 := by
  apply Matrix.inv_eq_left_inv
  rw [neg_mul, square_omegaA5, neg_neg]

private lemma lambda_omegaA5 : HasLambda omegaA5 (-1) := by
  intro μ
  rw [inverse_omegaA5]
  ext i j
  fin_cases μ <;> fin_cases i <;> fin_cases j <;>
    norm_num [omegaA0, omegaA5, omegaA5Z, omegaG05, omegaG05Z, mgammaR, mgammaZ, mgamma5Z, minkowskiMat, minkowskiR, minkowskiZ, Matrix.mul_apply, Fin.sum_univ_succ, Matrix.one_apply]



private lemma pin_omegaA5 : IsPin omegaA5 := by
  have hd : omegaA5.det * omegaA5.det = 1 := by
    simpa [Matrix.det_neg, show (-1 : ℝ) ^ 4 = 1 by norm_num] using congrArg Matrix.det square_omegaA5
  have hu : IsUnit omegaA5.det := isUnit_iff_ne_zero.mpr (by intro hz; simp [hz] at hd)
  have ha : |omegaA5.det| = 1 := by
    have hh : |omegaA5.det| * |omegaA5.det| = 1 := by
      simpa only [abs_mul, abs_one] using congrArg abs hd
    nlinarith [abs_nonneg omegaA5.det]
  exact ⟨hu, ha, (-1), lambda_omegaA5⟩



private lemma square_omegaG05 : omegaG05 * omegaG05 = -1 := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    norm_num [omegaA0, omegaA5, omegaA5Z, omegaG05, omegaG05Z, mgammaR, mgammaZ, mgamma5Z, Matrix.mul_apply, Fin.sum_univ_succ]

private lemma inverse_omegaG05 : omegaG05⁻¹ = -omegaG05 := by
  apply Matrix.inv_eq_left_inv
  rw [neg_mul, square_omegaG05, neg_neg]

private lemma lambda_omegaG05 : HasLambda omegaG05 (-minkowskiMat) := by
  intro μ
  rw [inverse_omegaG05]
  ext i j
  fin_cases μ <;> fin_cases i <;> fin_cases j <;>
    norm_num [omegaA0, omegaA5, omegaA5Z, omegaG05, omegaG05Z, mgammaR, mgammaZ, mgamma5Z, minkowskiMat, minkowskiR, minkowskiZ, Matrix.mul_apply, Fin.sum_univ_succ, Matrix.one_apply]



private lemma pin_omegaG05 : IsPin omegaG05 := by
  have hd : omegaG05.det * omegaG05.det = 1 := by
    simpa [Matrix.det_neg, show (-1 : ℝ) ^ 4 = 1 by norm_num] using congrArg Matrix.det square_omegaG05
  have hu : IsUnit omegaG05.det := isUnit_iff_ne_zero.mpr (by intro hz; simp [hz] at hd)
  have ha : |omegaG05.det| = 1 := by
    have hh : |omegaG05.det| * |omegaG05.det| = 1 := by
      simpa only [abs_mul, abs_one] using congrArg abs hd
    nlinarith [abs_nonneg omegaG05.det]
  exact ⟨hu, ha, (-minkowskiMat), lambda_omegaG05⟩



private lemma pin_one : IsPin (1 : Matrix (Fin 4) (Fin 4) ℝ) := by
  refine ⟨by simp, by simp, 1, ?_⟩
  intro μ
  simp [Matrix.one_apply]

private lemma pin_neg (S : Matrix (Fin 4) (Fin 4) ℝ) (h : IsPin S) : IsPin (-S) := by
  rcases h with ⟨hu, ha, Λ, hl⟩
  have hn : (-S)⁻¹ = -S⁻¹ := by
    apply Matrix.inv_eq_left_inv
    simp [Matrix.nonsing_inv_mul S hu]
  refine ⟨?_, ?_, Λ, ?_⟩
  · simpa [Matrix.det_neg, show (-1 : ℝ) ^ 4 = 1 by norm_num] using hu
  · simpa [Matrix.det_neg, show (-1 : ℝ) ^ 4 = 1 by norm_num] using ha
  · intro μ
    simpa only [hn, neg_mul, mul_neg, neg_neg] using hl μ

theorem solution : ∀ S ∈ OmegaPin, IsPin S := by
  intro S h
  simp only [OmegaPin, Set.mem_insert_iff, Set.mem_singleton_iff] at h
  rcases h with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact pin_one
  · exact pin_neg _ pin_one
  · exact pin_omegaA0
  · exact pin_neg _ pin_omegaA0
  · exact pin_omegaG05
  · exact pin_neg _ pin_omegaG05
  · exact pin_omegaA5
  · exact pin_neg _ pin_omegaA5

#print axioms solution
