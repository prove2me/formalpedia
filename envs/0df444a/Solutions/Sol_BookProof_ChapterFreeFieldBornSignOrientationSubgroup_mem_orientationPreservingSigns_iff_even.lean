-- Prove2me | solution 1 for BookProof.ChapterFreeFieldBornSignOrientationSubgroup.mem_orientationPreservingSigns_iff_even
-- status  : ACCEPTED   (prove)
-- author  : @miao
-- created : 2026-10-06T18:03:13.589522+00:00
-- url     : https://prove2.me/submissions/8cb853e5-d1cd-46e9-ac93-9e7950196295

import Definitions.Def_ChapterFreeFieldBornSignOrientationSubgroup
open BookProof.ChapterFreeFieldBornSignOrientationSubgroup
open BookProof.ChapterFreeFieldBornSignHom BookProof.ChapterFreeFieldBornSignMatrix
open BookProof.ChapterFreeFieldBornSignAction
variable {n : ℕ}

theorem solution (b : Fin n → Bool) :
    b ∈ orientationPreservingSigns n ↔ Even (flipCount b) := by
  have ho : flipMatrix b ∈ Matrix.orthogonalGroup (Fin n) ℝ := by
    rw [Matrix.mem_orthogonalGroup_iff, flipMatrix, Matrix.diagonal_transpose,
      Matrix.diagonal_mul_diagonal]
    have h : (fun k => flipVec b k * flipVec b k) = fun _ => (1 : ℝ) := by
      funext k
      cases h : b k <;> simp [flipVec, h]
    rw [h, Matrix.diagonal_one]
  have hd : (flipMatrix b).det = (-1 : ℝ) ^ flipCount b := by
    classical
    simp only [flipMatrix, Matrix.det_diagonal, flipVec, flipCount]
    rw [Finset.prod_ite]
    simp
  rw [mem_orientationPreservingSigns_iff, Matrix.mem_specialOrthogonalGroup_iff]
  simp only [ho, true_and, hd]
  exact neg_one_pow_eq_one_iff_even (by norm_num)

#print axioms solution
