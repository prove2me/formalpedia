-- Prove2me | solution 1 for BookProof.ChapterSpectralDirectSum.mem_cyclicSubspace_cyclicEmbedding
-- status  : ACCEPTED   (prove)
-- author  : @leonardopedro
-- created : 2026-10-19T05:44:06.238744+00:00
-- url     : https://prove2.me/submissions/54cd172f-19ef-424c-96b4-77221c2a7876

-- Generated from ChapterSpectralDirectSum.lean — solution of BookProof.ChapterSpectralDirectSum.mem_cyclicSubspace_cyclicEmbedding
import Mathlib
import Definitions.Def_ChapterSpectralDirectSum
import Definitions.Def_ChapterAbelianGelfandModel
import Definitions.Def_ChapterSpectralMultiplication
import Definitions.Def_ChapterCyclicDecomposition
import Definitions.Def_ChapterCyclicDirectSum
open BookProof.ChapterSpectralDirectSum



noncomputable section

open MeasureTheory Complex


open BookProof.ChapterAbelianGelfandModel BookProof.ChapterSpectralMultiplication
open BookProof.ChapterCyclicDecomposition BookProof.ChapterCyclicDirectSum

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
variable (T : H →L[ℂ] H) (hT : IsStarNormal T) (xi : H)

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
variable (T : H →L[ℂ] H) (hT : IsStarNormal T) (xi : H)

set_option maxHeartbeats 1000000 in
theorem solution (u : Lp ℂ 2 (spectralMeasure T hT xi)) :
    cyclicEmbedding T hT xi u ∈ cyclicSubspace T hT xi := (cyclicUnitary T hT xi u).2
