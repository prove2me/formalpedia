-- Prove2me | solution 1 for BookProof.ChapterSirkGramWhitening.whitened_apply
-- status  : ACCEPTED   (prove)
-- author  : @leonardopedro
-- created : 2026-09-10T06:45:09.970542+00:00
-- url     : https://prove2.me/submissions/ca4a5dac-c5b0-4b20-a102-8bfe1710ddda

-- Generated from ChapterSirkGramWhitening.lean — solution of BookProof.ChapterSirkGramWhitening.whitened_apply
import Mathlib
import Definitions.Def_ChapterSirkGramWhitening
open BookProof.ChapterSirkGramWhitening









noncomputable section


open scoped InnerProductSpace
open Matrix
open BookProof.ChapterH4 BookProof.ChapterSirkWhitening

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℂ E] [CompleteSpace E]

set_option maxHeartbeats 1000000 in
theorem solution {m : ℕ} (w : Fin m → E)
    (T : EuclideanSpace ℂ (Fin m) →L[ℂ] EuclideanSpace ℂ (Fin m))
    (c : EuclideanSpace ℂ (Fin m)) : whitened w T c = synthesis w (T c) := rfl
