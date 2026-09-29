-- Prove2me | solution 1 for BookProof.ChapterSirkGramWhitening.isWhitening_of_matrix
-- status  : ACCEPTED   (prove)
-- author  : @leonardopedro
-- created : 2026-09-10T08:02:49.063876+00:00
-- url     : https://prove2.me/submissions/64c1a503-227f-48eb-ba7b-d97846dead69

-- Generated from ChapterSirkGramWhitening.lean — solution of BookProof.ChapterSirkGramWhitening.isWhitening_of_matrix
import Mathlib
import Definitions.Def_ChapterSirkGramWhitening
import Theorems.Thm_BookProof_ChapterSirkGramWhitening_gramOp_eq_toEuclideanCLM
open BookProof.ChapterSirkGramWhitening









noncomputable section


open scoped InnerProductSpace
open Matrix
open BookProof.ChapterH4 BookProof.ChapterSirkWhitening

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℂ E] [CompleteSpace E]

set_option maxHeartbeats 1000000 in
theorem solution {m : ℕ} (w : Fin m → E) {M : Matrix (Fin m) (Fin m) ℂ}
    (hM : IsWhiteningMatrix w M) :
    IsWhitening w (Matrix.toEuclideanCLM (𝕜 := ℂ) M) := by

  have hstar : ContinuousLinearMap.adjoint (Matrix.toEuclideanCLM (𝕜 := ℂ) M)
      = Matrix.toEuclideanCLM (𝕜 := ℂ) Mᴴ := by
    have : star (Matrix.toEuclideanCLM (𝕜 := ℂ) M)
        = Matrix.toEuclideanCLM (𝕜 := ℂ) (star M) := (map_star _ _).symm
    simpa [ContinuousLinearMap.star_eq_adjoint, Matrix.star_eq_conjTranspose] using this
  rw [IsWhitening, gramOp_eq_toEuclideanCLM, hstar]
  have hmul : ∀ P Q : Matrix (Fin m) (Fin m) ℂ,
      (Matrix.toEuclideanCLM (𝕜 := ℂ) P).comp (Matrix.toEuclideanCLM (𝕜 := ℂ) Q)
        = Matrix.toEuclideanCLM (𝕜 := ℂ) (P * Q) := by
    intro P Q
    exact (map_mul (Matrix.toEuclideanCLM (𝕜 := ℂ) (n := Fin m)) P Q).symm
  rw [hmul, hmul, ← mul_assoc, hM]
  have hone : Matrix.toEuclideanCLM (𝕜 := ℂ) (1 : Matrix (Fin m) (Fin m) ℂ)
      = ContinuousLinearMap.id ℂ (EuclideanSpace ℂ (Fin m)) := by
    exact map_one (Matrix.toEuclideanCLM (𝕜 := ℂ) (n := Fin m))
  exact hone
