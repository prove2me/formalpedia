-- Prove2me | solution 1 for BookProof.ChapterSirkGramWhitening.gramMatrix_conjTranspose
-- status  : ACCEPTED   (prove)
-- author  : @leonardopedro
-- created : 2026-09-10T06:31:22.25266+00:00
-- url     : https://prove2.me/submissions/3bb7a027-e5b8-4003-aa26-a893b98e79fc

-- Generated from ChapterSirkGramWhitening.lean — solution of BookProof.ChapterSirkGramWhitening.gramMatrix_conjTranspose
import Mathlib
import Definitions.Def_ChapterSirkGramWhitening
open BookProof.ChapterSirkGramWhitening









noncomputable section


open scoped InnerProductSpace
open Matrix
open BookProof.ChapterH4 BookProof.ChapterSirkWhitening

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℂ E] [CompleteSpace E]

set_option maxHeartbeats 1000000 in
theorem solution {m : ℕ} (w : Fin m → E) :
    (gramMatrix w)ᴴ = gramMatrix w := by

  ext i j
  simp [gramMatrix, Matrix.conjTranspose_apply]
