-- Prove2me | solution 1 for BookProof.ChapterCyclicDecomposition.isClosed_cyclicSubspace
-- status  : ACCEPTED   (prove)
-- author  : @leonardopedro
-- created : 2026-10-17T01:51:22.056039+00:00
-- url     : https://prove2.me/submissions/536ea3c7-0df6-47bf-b04f-ca821c6e8100

-- Generated from ChapterCyclicDecomposition.lean — solution of BookProof.ChapterCyclicDecomposition.isClosed_cyclicSubspace
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
theorem solution (xi : H) : IsClosed (cyclicSubspace T hT xi : Set H) := Submodule.isClosed_topologicalClosure _
