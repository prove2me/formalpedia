-- Prove2me | solution 1 for BookProof.ChapterH8.krylovEmbedding_range
-- status  : ACCEPTED   (prove)
-- author  : @leonardopedro
-- created : 2026-11-03T21:58:30.537204+00:00
-- url     : https://prove2.me/submissions/e0007a2e-69b1-45cf-b4f0-bd8809536510

-- Generated from ChapterH8Bases.lean — solution of BookProof.ChapterH8.krylovEmbedding_range
import Mathlib
import Definitions.Def_ChapterH8Bases
import Theorems.Thm_BookProof_ChapterH8_orthonormalEmbedding_range
import Theorems.Thm_BookProof_ChapterH8_krylovOrthonormal_span
open BookProof.ChapterH8



noncomputable section


open BookProof.ChapterH4 BookProof.ChapterH5 BookProof.ChapterH6



variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℂ E] [CompleteSpace E]

open ContinuousLinearMap

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℂ E] [CompleteSpace E]

set_option maxHeartbeats 1000000 in
theorem solution (H : E →ₗ[ℂ] E) (v : E) {n : ℕ}
    (hli : LinearIndependent ℂ (fun i : Fin n => (H ^ (i : ℕ)) v)) :
    LinearMap.range (krylovEmbedding H v hli : EuclideanSpace ℂ (Fin n) →ₗ[ℂ] E)
      = krylovSpan H v n := by

  rw [krylovEmbedding, orthonormalEmbedding_range, krylovOrthonormal_span]
