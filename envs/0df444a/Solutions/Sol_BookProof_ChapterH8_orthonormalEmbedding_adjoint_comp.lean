-- Prove2me | solution 1 for BookProof.ChapterH8.orthonormalEmbedding_adjoint_comp
-- status  : ACCEPTED   (prove)
-- author  : @fizzyinc3
-- created : 2026-10-25T06:37:35.116877+00:00
-- url     : https://prove2.me/submissions/11ae8729-b3a8-405e-b9d5-2ed6eff79f3d

import Definitions.Def_ChapterH4
import Definitions.Def_ChapterH5
import Definitions.Def_ChapterH6
import Mathlib
import Definitions.Def_ChapterH8Bases
import Definitions.Def_ChapterH8
import Definitions.Def_ChapterShiftedQuadraticEsa
-- Generated from ChapterH8Bases.lean — theorem BookProof.ChapterH8.orthonormalEmbedding_adjoint_comp
open BookProof.ChapterH8


noncomputable section


open BookProof.ChapterH4 BookProof.ChapterH5 BookProof.ChapterH6



variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℂ E] [CompleteSpace E]

open ContinuousLinearMap
theorem solution {m : ℕ} (w : Fin m → E) (hw : Orthonormal ℂ w) :
    (adjoint (orthonormalEmbedding w hw)).comp (orthonormalEmbedding w hw)
      = ContinuousLinearMap.id ℂ (EuclideanSpace ℂ (Fin m)) := by
  ext1 x
  refine ext_inner_left ℂ fun y => ?_
  rw [ContinuousLinearMap.comp_apply, ContinuousLinearMap.adjoint_inner_right]
  change inner ℂ (orthonormalEmbeddingLI w hw y) (orthonormalEmbeddingLI w hw x) = _
  rw [LinearIsometry.inner_map_map]
  rfl
