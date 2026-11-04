-- Prove2me | solution 1 for BookProof.ChapterH8.orthonormalEmbedding_inner
-- status  : ACCEPTED   (prove)
-- author  : @leonardopedro
-- created : 2026-11-03T21:57:54.935189+00:00
-- url     : https://prove2.me/submissions/64b007fd-f9ee-4df2-b3cf-82686d0ca83f

-- Generated from ChapterH8Bases.lean — solution of BookProof.ChapterH8.orthonormalEmbedding_inner
import Mathlib
import Definitions.Def_ChapterH8Bases
open BookProof.ChapterH8



noncomputable section


open BookProof.ChapterH4 BookProof.ChapterH5 BookProof.ChapterH6



variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℂ E] [CompleteSpace E]

open ContinuousLinearMap

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℂ E] [CompleteSpace E]

set_option maxHeartbeats 1000000 in
theorem solution {m : ℕ} (w : Fin m → E) (hw : Orthonormal ℂ w)
    (x y : EuclideanSpace ℂ (Fin m)) :
    inner ℂ (orthonormalEmbedding w hw x) (orthonormalEmbedding w hw y) = inner ℂ x y := (orthonormalEmbeddingLI w hw).inner_map_map x y
