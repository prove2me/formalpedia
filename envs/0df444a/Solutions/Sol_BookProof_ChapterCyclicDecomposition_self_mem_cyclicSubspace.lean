-- Prove2me | solution 1 for BookProof.ChapterCyclicDecomposition.self_mem_cyclicSubspace
-- status  : ACCEPTED   (prove)
-- author  : @leonardopedro
-- created : 2026-10-17T01:51:24.20232+00:00
-- url     : https://prove2.me/submissions/3a2d7128-0395-4f88-8a61-4ff9791f66b6

-- Generated from ChapterCyclicDecomposition.lean — solution of BookProof.ChapterCyclicDecomposition.self_mem_cyclicSubspace
import Mathlib
import Definitions.Def_ChapterCyclicDecomposition
import Theorems.Thm_BookProof_ChapterCyclicDecomposition_cfcHom_apply_mem_cyclicSubspace
import Definitions.Def_ChapterSpectralMultiplication
open BookProof.ChapterCyclicDecomposition



noncomputable section

open MeasureTheory Complex


open BookProof.ChapterSpectralMultiplication

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
variable (T : H →L[ℂ] H) (hT : IsStarNormal T)

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
variable (T : H →L[ℂ] H) (hT : IsStarNormal T)

set_option maxHeartbeats 1000000 in
theorem solution (xi : H) : xi ∈ cyclicSubspace T hT xi := by

  have h := cfcHom_apply_mem_cyclicSubspace T hT xi 1
  rwa [map_one] at h
