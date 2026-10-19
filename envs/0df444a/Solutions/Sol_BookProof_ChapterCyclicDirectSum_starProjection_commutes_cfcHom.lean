-- Prove2me | solution 1 for BookProof.ChapterCyclicDirectSum.starProjection_commutes_cfcHom
-- status  : ACCEPTED   (prove)
-- author  : @leonardopedro
-- created : 2026-10-17T02:17:49.444975+00:00
-- url     : https://prove2.me/submissions/f76c0621-a2b0-4088-a80a-9ad4e800129f

-- Generated from ChapterCyclicDirectSum.lean — solution of BookProof.ChapterCyclicDirectSum.starProjection_commutes_cfcHom
import Mathlib
import Definitions.Def_ChapterCyclicDirectSum
import Theorems.Thm_BookProof_ChapterCyclicDecomposition_invariant_orthogonal
import Definitions.Def_ChapterCyclicDecomposition
open BookProof.ChapterCyclicDirectSum



noncomputable section

open MeasureTheory Complex


open BookProof.ChapterCyclicDecomposition

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
variable (T : H →L[ℂ] H) (hT : IsStarNormal T)

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
variable (T : H →L[ℂ] H) (hT : IsStarNormal T)

set_option maxHeartbeats 1000000 in
theorem solution {M : Submodule ℂ H} [M.HasOrthogonalProjection]
    (hM : Invariant T hT M) (g : C(spectrum ℂ T, ℂ)) (v : H) :
    M.starProjection (cfcHom hT g v) = cfcHom hT g (M.starProjection v) := by

  refine Submodule.eq_starProjection_of_mem_orthogonal'
    (hM g _ (M.starProjection_apply_mem v))
    (invariant_orthogonal T hT hM g _ (M.sub_starProjection_mem_orthogonal v)) ?_
  rw [← map_add]
  congr 1
  abel
