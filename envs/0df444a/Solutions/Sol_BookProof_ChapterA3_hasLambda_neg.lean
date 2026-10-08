-- Prove2me | solution 1 for BookProof.ChapterA3.hasLambda_neg
-- status  : ACCEPTED   (prove)
-- author  : @miao
-- created : 2026-10-06T18:05:18.590647+00:00
-- url     : https://prove2.me/submissions/c07416d4-4ef9-42f8-9d77-72c4518a189d

import Mathlib
import Definitions.Def_ChapterA3c
open BookProof.ChapterA3 Matrix

private lemma inverse_neg (S : Matrix (Fin 4) (Fin 4) ℝ) : (-S)⁻¹ = -S⁻¹ := by
  by_cases h : IsUnit S.det
  · apply Matrix.inv_eq_left_inv
    simpa using Matrix.nonsing_inv_mul S h
  · rw [Matrix.nonsing_inv_apply_not_isUnit S h,
      Matrix.nonsing_inv_apply_not_isUnit (-S)]
    · simp
    · simpa [Matrix.det_neg] using h

theorem solution {S Λ : Matrix (Fin 4) (Fin 4) ℝ} (h : HasLambda S Λ) :
    HasLambda (-S) Λ := by
  intro μ
  simpa [inverse_neg, neg_mul, mul_neg] using h μ

#print axioms solution
