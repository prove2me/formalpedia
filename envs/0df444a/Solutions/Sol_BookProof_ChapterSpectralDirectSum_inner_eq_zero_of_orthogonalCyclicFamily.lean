-- Prove2me | solution 1 for BookProof.ChapterSpectralDirectSum.inner_eq_zero_of_orthogonalCyclicFamily
-- status  : ACCEPTED   (prove)
-- author  : @leonardopedro
-- created : 2026-10-19T05:44:10.578722+00:00
-- url     : https://prove2.me/submissions/ee50c134-da7b-4709-9f32-2cd0c76f6564

-- Generated from ChapterSpectralDirectSum.lean — solution of BookProof.ChapterSpectralDirectSum.inner_eq_zero_of_orthogonalCyclicFamily
import Mathlib
import Definitions.Def_ChapterSpectralDirectSum
import Theorems.Thm_BookProof_ChapterSpectralDirectSum_inner_eq_zero_of_le_orthogonal
import Theorems.Thm_BookProof_ChapterCyclicDecomposition_self_mem_cyclicSubspace
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
theorem solution {S : Set H} (hS : OrthogonalCyclicFamily T hT S)
    {x y : H} (hx : x ∈ S) (hy : y ∈ S) (hxy : x ≠ y) : inner ℂ x y = (0 : ℂ) :=
  inner_eq_zero_of_le_orthogonal (hS.2 x hx y hy hxy) (self_mem_cyclicSubspace T hT x)
      (self_mem_cyclicSubspace T hT y)
