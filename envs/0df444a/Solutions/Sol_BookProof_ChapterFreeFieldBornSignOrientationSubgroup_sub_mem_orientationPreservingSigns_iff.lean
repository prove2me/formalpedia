-- Prove2me | solution 1 for BookProof.ChapterFreeFieldBornSignOrientationSubgroup.sub_mem_orientationPreservingSigns_iff
-- status  : ACCEPTED   (prove)
-- author  : @miao
-- created : 2026-10-06T18:03:15.697922+00:00
-- url     : https://prove2.me/submissions/68972920-701d-4474-b9d7-9c6e053e2e3f

import Definitions.Def_ChapterFreeFieldBornSignOrientationSubgroup
open BookProof.ChapterFreeFieldBornSignOrientationSubgroup
open BookProof.ChapterFreeFieldBornSignHom BookProof.ChapterFreeFieldBornSignMatrix
open BookProof.ChapterFreeFieldBornSignAction
variable {n : ℕ}

private lemma orthogonal (b : Fin n → Bool) :
    flipMatrix b ∈ Matrix.orthogonalGroup (Fin n) ℝ := by
  rw [Matrix.mem_orthogonalGroup_iff, flipMatrix, Matrix.diagonal_transpose,
    Matrix.diagonal_mul_diagonal]
  have h : (fun k => flipVec b k * flipVec b k) = fun _ => (1 : ℝ) := by
    funext k
    cases h : b k <;> simp [flipVec, h]
  rw [h, Matrix.diagonal_one]

private lemma mem_iff (b : Fin n → Bool) :
    b ∈ orientationPreservingSigns n ↔ (∏ k, flipVec b k) = 1 := by
  rw [mem_orientationPreservingSigns_iff, Matrix.mem_specialOrthogonalGroup_iff]
  simp only [orthogonal b, true_and]
  rw [flipMatrix, Matrix.det_diagonal]

private lemma char_pm (b : Fin n → Bool) :
    (∏ k, flipVec b k) = (1 : ℝ) ∨ (∏ k, flipVec b k) = -1 := by
  classical
  have hd : (∏ k, flipVec b k) = (-1 : ℝ) ^ flipCount b := by
    simp only [flipVec, flipCount]
    rw [Finset.prod_ite]
    simp
  rw [hd]
  exact neg_one_pow_eq_or ℝ _

private lemma char_sub (b₁ b₂ : Fin n → Bool) :
    (∏ k, flipVec (b₁ - b₂) k) = (∏ k, flipVec b₁ k) * (∏ k, flipVec b₂ k) := by
  rw [← Finset.prod_mul_distrib]
  apply Finset.prod_congr rfl
  intro k _
  change (if b₁ k - b₂ k then (-1 : ℝ) else 1) = _
  cases h₁ : b₁ k <;> cases h₂ : b₂ k <;> simp [flipVec, h₁, h₂]

theorem solution (b₁ b₂ : Fin n → Bool) :
    b₁ - b₂ ∈ orientationPreservingSigns n ↔
      (b₁ ∈ orientationPreservingSigns n ↔ b₂ ∈ orientationPreservingSigns n) := by
  rw [mem_iff, mem_iff, mem_iff, char_sub]
  rcases char_pm b₁ with h₁ | h₁ <;> rcases char_pm b₂ with h₂ | h₂ <;>
    norm_num [h₁, h₂]

#print axioms solution
