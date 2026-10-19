-- Prove2me | solution 1 for BookProof.ChapterCyclicDecomposition.cfcHom_apply_mem_cyclicSubspace
-- status  : ACCEPTED   (prove)
-- author  : @leonardopedro
-- created : 2026-10-17T01:51:23.208536+00:00
-- url     : https://prove2.me/submissions/abcb6573-a55f-46f1-a053-532aa082640e

-- Generated from ChapterCyclicDecomposition.lean — solution of BookProof.ChapterCyclicDecomposition.cfcHom_apply_mem_cyclicSubspace
import Mathlib
import Definitions.Def_ChapterCyclicDecomposition
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
theorem solution (xi : H) (g : C(spectrum ℂ T, ℂ)) :
    cfcHom hT g xi ∈ cyclicSubspace T hT xi := Submodule.le_topologicalClosure _ (Submodule.subset_span ⟨g, rfl⟩)
