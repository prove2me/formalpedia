-- Prove2me | solution 1 for BookProof.ChapterSirkGramWhitening.isWhiteningMatrix_one_of_orthonormal
-- status  : ACCEPTED   (prove)
-- author  : @leonardopedro
-- created : 2026-09-10T06:35:57.216159+00:00
-- url     : https://prove2.me/submissions/37c64e37-2b04-4631-8d3d-233e0fa1da1a

-- Generated from ChapterSirkGramWhitening.lean — solution of BookProof.ChapterSirkGramWhitening.isWhiteningMatrix_one_of_orthonormal
import Mathlib
import Definitions.Def_ChapterSirkGramWhitening
open BookProof.ChapterSirkGramWhitening









noncomputable section


open scoped InnerProductSpace
open Matrix
open BookProof.ChapterH4 BookProof.ChapterSirkWhitening

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℂ E] [CompleteSpace E]

set_option maxHeartbeats 1000000 in
theorem solution {m : ℕ} {w : Fin m → E}
    (hw : Orthonormal ℂ w) : IsWhiteningMatrix w 1 := by

  have hG : gramMatrix w = 1 := by
    ext i j
    rw [gramMatrix, orthonormal_iff_ite.mp hw i j]
    simp [Matrix.one_apply]
  simp [IsWhiteningMatrix, hG]
