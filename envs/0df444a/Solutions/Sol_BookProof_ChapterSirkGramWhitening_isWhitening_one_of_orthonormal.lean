-- Prove2me | solution 1 for BookProof.ChapterSirkGramWhitening.isWhitening_one_of_orthonormal
-- status  : ACCEPTED   (prove)
-- author  : @leonardopedro
-- created : 2026-09-10T08:07:23.219829+00:00
-- url     : https://prove2.me/submissions/9e62d1ea-fe73-44c6-b538-4b8a4d011781

-- Generated from ChapterSirkGramWhitening.lean — solution of BookProof.ChapterSirkGramWhitening.isWhitening_one_of_orthonormal
import Mathlib
import Definitions.Def_ChapterSirkGramWhitening
import Theorems.Thm_BookProof_ChapterSirkGramWhitening_isWhitening_of_matrix
import Theorems.Thm_BookProof_ChapterSirkGramWhitening_isWhiteningMatrix_one_of_orthonormal
open BookProof.ChapterSirkGramWhitening









noncomputable section


open scoped InnerProductSpace
open Matrix
open BookProof.ChapterH4 BookProof.ChapterSirkWhitening

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℂ E] [CompleteSpace E]

set_option maxHeartbeats 1000000 in
theorem solution {m : ℕ} {w : Fin m → E} (hw : Orthonormal ℂ w) :
    IsWhitening w (Matrix.toEuclideanCLM (𝕜 := ℂ) (1 : Matrix (Fin m) (Fin m) ℂ)) := isWhitening_of_matrix w (isWhiteningMatrix_one_of_orthonormal hw)
