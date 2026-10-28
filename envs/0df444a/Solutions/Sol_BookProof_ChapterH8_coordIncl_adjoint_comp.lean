-- Prove2me | solution 1 for BookProof.ChapterH8.coordIncl_adjoint_comp
-- status  : ACCEPTED   (prove)
-- author  : @fizzyinc3
-- created : 2026-10-25T06:37:43.572191+00:00
-- url     : https://prove2.me/submissions/984f67c5-da19-4830-bf50-078319b5a226

import Definitions.Def_ChapterH4
import Definitions.Def_ChapterH5
import Definitions.Def_ChapterH6
import Mathlib
import Definitions.Def_ChapterH8Bases
import Definitions.Def_ChapterH8
import Definitions.Def_ChapterShiftedQuadraticEsa
-- Generated from ChapterH8Bases.lean — theorem BookProof.ChapterH8.coordIncl_adjoint_comp
open BookProof.ChapterH8


noncomputable section


open BookProof.ChapterH4 BookProof.ChapterH5 BookProof.ChapterH6



variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℂ E] [CompleteSpace E]

open ContinuousLinearMap
theorem solution {m n : ℕ} (hmn : m ≤ n) :
    (adjoint (coordIncl hmn)).comp (coordIncl hmn)
      = ContinuousLinearMap.id ℂ (EuclideanSpace ℂ (Fin m)) := by
  ext1 x
  refine ext_inner_left ℂ fun y => ?_
  rw [ContinuousLinearMap.comp_apply, ContinuousLinearMap.adjoint_inner_right]
  unfold coordIncl orthonormalEmbedding
  rw [LinearIsometry.coe_toContinuousLinearMap, LinearIsometry.inner_map_map]
  rfl
