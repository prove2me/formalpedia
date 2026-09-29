-- Prove2me | solution 1 for BookProof.ChapterSirkGramWhitening.onbEmbedding_apply
-- status  : ACCEPTED   (prove)
-- author  : @leonardopedro
-- created : 2026-09-10T06:37:26.847282+00:00
-- url     : https://prove2.me/submissions/f00edc57-95ac-41c6-928a-5649cbf0027a

-- Generated from ChapterSirkGramWhitening.lean — solution of BookProof.ChapterSirkGramWhitening.onbEmbedding_apply
import Mathlib
import Definitions.Def_ChapterSirkGramWhitening
open BookProof.ChapterSirkGramWhitening









noncomputable section


open scoped InnerProductSpace
open Matrix
open BookProof.ChapterH4 BookProof.ChapterSirkWhitening

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℂ E] [CompleteSpace E]

set_option maxHeartbeats 1000000 in
theorem solution {d : ℕ} (S : Submodule ℂ E) [CompleteSpace S]
    (b : OrthonormalBasis (Fin d) ℂ S) (c : EuclideanSpace ℂ (Fin d)) :
    onbEmbedding S b c = (b.repr.symm c : E) := rfl
