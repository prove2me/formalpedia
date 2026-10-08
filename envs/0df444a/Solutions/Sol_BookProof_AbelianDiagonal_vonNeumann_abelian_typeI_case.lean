-- Prove2me | solution 1 for BookProof.AbelianDiagonal.vonNeumann_abelian_typeI_case
-- status  : ACCEPTED   (prove)
-- author  : @miao
-- created : 2026-10-07T05:50:44.524618+00:00
-- url     : https://prove2.me/submissions/1c469b2d-371b-4dac-a343-a6ed750fb494

import Mathlib
import Definitions.Def_ChapterAbelianDiagonal
open Matrix BookProof.AbelianDiagonal
variable {n : Type*} [Fintype n] [DecidableEq n]

private lemma commute (d e : n → ℂ) :
    Matrix.diagonal d * Matrix.diagonal e = Matrix.diagonal e * Matrix.diagonal d := by
  rw [Matrix.diagonal_mul_diagonal, Matrix.diagonal_mul_diagonal]
  congr 1
  funext i
  exact mul_comm _ _

private lemma diagonal_of_commute (M : Matrix n n ℂ)
    (h : ∀ d : n → ℂ, M * Matrix.diagonal d = Matrix.diagonal d * M) :
    M = Matrix.diagonal (fun i => M i i) := by
  ext i j
  by_cases hij : i = j
  · subst j; simp
  · have he := congrArg (fun A : Matrix n n ℂ => A i j) (h (fun k => if k = j then 1 else 0))
    simpa [Matrix.mul_diagonal, Matrix.diagonal_mul, hij] using he

theorem solution :
    Function.Injective (diagonalStarAlgHom : (n → ℂ) →⋆ₐ[ℂ] Matrix n n ℂ) ∧
      (∀ d e : n → ℂ,
        Matrix.diagonal d * Matrix.diagonal e = Matrix.diagonal e * Matrix.diagonal d) ∧
      (∀ M : Matrix n n ℂ,
        (∀ d : n → ℂ, M * Matrix.diagonal d = Matrix.diagonal d * M) ↔
          ∃ e : n → ℂ, M = Matrix.diagonal e) := by
  refine ⟨?_, commute, ?_⟩
  · intro d e h
    funext i
    have hi := congrArg (fun M : Matrix n n ℂ => M i i) h
    simpa [diagonalStarAlgHom] using hi
  · intro M
    constructor
    · intro h
      exact ⟨fun i => M i i, diagonal_of_commute M h⟩
    · rintro ⟨e, rfl⟩ d
      exact commute e d

#print axioms solution
