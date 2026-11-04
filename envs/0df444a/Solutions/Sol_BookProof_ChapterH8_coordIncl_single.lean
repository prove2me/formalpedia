-- Prove2me | solution 1 for BookProof.ChapterH8.coordIncl_single
-- status  : ACCEPTED   (prove)
-- author  : @leonardopedro
-- created : 2026-11-03T21:58:12.477343+00:00
-- url     : https://prove2.me/submissions/c9b9431e-0177-4452-bb3b-207572ff7df4

-- Generated from ChapterH8Bases.lean — solution of BookProof.ChapterH8.coordIncl_single
import Mathlib
import Definitions.Def_ChapterH8Bases
import Theorems.Thm_BookProof_ChapterH8_orthonormalEmbedding_single
open BookProof.ChapterH8



noncomputable section


open BookProof.ChapterH4 BookProof.ChapterH5 BookProof.ChapterH6



variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℂ E] [CompleteSpace E]

open ContinuousLinearMap

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℂ E] [CompleteSpace E]

set_option maxHeartbeats 1000000 in
theorem solution {m n : ℕ} (hmn : m ≤ n) (i : Fin m) :
    coordIncl hmn (EuclideanSpace.single i (1 : ℂ))
      = EuclideanSpace.single (Fin.castLE hmn i) (1 : ℂ) := orthonormalEmbedding_single _ _ i
