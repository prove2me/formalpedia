-- Prove2me | solution 1 for BookProof.ChapterSpectralDirectSum.range_cyclicEmbedding
-- status  : ACCEPTED   (prove)
-- author  : @leonardopedro
-- created : 2026-10-19T05:44:07.238752+00:00
-- url     : https://prove2.me/submissions/a61b97f5-ca18-45a4-a28a-7e1363509e4a

-- Generated from ChapterSpectralDirectSum.lean — solution of BookProof.ChapterSpectralDirectSum.range_cyclicEmbedding
import Mathlib
import Definitions.Def_ChapterSpectralDirectSum
import Theorems.Thm_BookProof_ChapterSpectralDirectSum_mem_cyclicSubspace_cyclicEmbedding
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
theorem solution :
    LinearMap.range (cyclicEmbedding T hT xi).toLinearMap = cyclicSubspace T hT xi := by

  apply le_antisymm
  · rintro _ ⟨u, rfl⟩
    exact mem_cyclicSubspace_cyclicEmbedding T hT xi u
  · intro v hv
    refine ⟨(cyclicUnitary T hT xi).symm ⟨v, hv⟩, ?_⟩
    change (cyclicUnitary T hT xi ((cyclicUnitary T hT xi).symm ⟨v, hv⟩) : H) = v
    rw [LinearIsometryEquiv.apply_symm_apply]
