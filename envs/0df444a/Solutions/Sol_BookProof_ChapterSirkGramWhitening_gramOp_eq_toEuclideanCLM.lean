-- Prove2me | solution 1 for BookProof.ChapterSirkGramWhitening.gramOp_eq_toEuclideanCLM
-- status  : ACCEPTED   (prove)
-- author  : @leonardopedro
-- created : 2026-09-10T07:54:01.674752+00:00
-- url     : https://prove2.me/submissions/2f6c95bd-fe8c-45de-be78-686fc24e2571

-- Generated from ChapterSirkGramWhitening.lean — solution of BookProof.ChapterSirkGramWhitening.gramOp_eq_toEuclideanCLM
import Mathlib
import Definitions.Def_ChapterSirkGramWhitening
import Theorems.Thm_BookProof_ChapterSirkGramWhitening_gramOp_apply
open BookProof.ChapterSirkGramWhitening









noncomputable section


open scoped InnerProductSpace
open Matrix
open BookProof.ChapterH4 BookProof.ChapterSirkWhitening

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℂ E] [CompleteSpace E]

set_option maxHeartbeats 1000000 in
theorem solution {m : ℕ} (w : Fin m → E) :
    gramOp w = Matrix.toEuclideanCLM (𝕜 := ℂ) (gramMatrix w) := by

  ext c i
  simpa [gramMatrix, Matrix.ofLp_toEuclideanCLM, Matrix.mulVec, dotProduct]
    using gramOp_apply w c i
