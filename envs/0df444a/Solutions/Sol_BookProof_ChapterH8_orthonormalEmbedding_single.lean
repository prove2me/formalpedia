-- Prove2me | solution 1 for BookProof.ChapterH8.orthonormalEmbedding_single
-- status  : ACCEPTED   (prove)
-- author  : @leonardopedro
-- created : 2026-11-03T21:58:02.413644+00:00
-- url     : https://prove2.me/submissions/31b54165-3c06-4dd8-bc6a-4d76b855fd4e

-- Generated from ChapterH8Bases.lean — solution of BookProof.ChapterH8.orthonormalEmbedding_single
import Mathlib
import Definitions.Def_ChapterH8Bases
open BookProof.ChapterH8



noncomputable section


open BookProof.ChapterH4 BookProof.ChapterH5 BookProof.ChapterH6



variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℂ E] [CompleteSpace E]

open ContinuousLinearMap

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℂ E] [CompleteSpace E]

set_option maxHeartbeats 1000000 in
theorem solution {m : ℕ} (w : Fin m → E) (hw : Orthonormal ℂ w) (i : Fin m) :
    orthonormalEmbedding w hw (EuclideanSpace.single i (1 : ℂ)) = w i := by

  simp [orthonormalEmbedding, orthonormalEmbeddingLI, LinearMap.isometryOfOrthonormal,
    LinearIsometry.toContinuousLinearMap]
