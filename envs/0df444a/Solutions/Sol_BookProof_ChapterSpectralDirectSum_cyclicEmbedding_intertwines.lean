-- Prove2me | solution 1 for BookProof.ChapterSpectralDirectSum.cyclicEmbedding_intertwines
-- status  : ACCEPTED   (prove)
-- author  : @leonardopedro
-- created : 2026-10-17T09:57:07.218428+00:00
-- url     : https://prove2.me/submissions/63411e21-fdc7-422f-90b1-75cab4c5c019

-- Generated from ChapterSpectralDirectSum.lean — solution of BookProof.ChapterSpectralDirectSum.cyclicEmbedding_intertwines
import Mathlib
import Definitions.Def_ChapterSpectralDirectSum
import Theorems.Thm_BookProof_ChapterSpectralDirectSum_cyclicEmbedding_intertwines_cfc
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
    cyclicEmbedding T hT xi (mulRep (spectralMeasure T hT xi) (coordFn T) u)
      = T (cyclicEmbedding T hT xi u) := by

  rw [cyclicEmbedding_intertwines_cfc T hT xi (coordFn T) u, cfcHom_coordFn]
