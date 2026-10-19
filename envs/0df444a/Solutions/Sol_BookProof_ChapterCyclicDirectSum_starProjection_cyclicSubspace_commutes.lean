-- Prove2me | solution 1 for BookProof.ChapterCyclicDirectSum.starProjection_cyclicSubspace_commutes
-- status  : ACCEPTED   (prove)
-- author  : @leonardopedro
-- created : 2026-10-17T02:17:51.783022+00:00
-- url     : https://prove2.me/submissions/b2ecdb65-2092-48de-943e-63f8e7d62a61

-- Generated from ChapterCyclicDirectSum.lean — solution of BookProof.ChapterCyclicDirectSum.starProjection_cyclicSubspace_commutes
import Mathlib
import Definitions.Def_ChapterCyclicDirectSum
import Theorems.Thm_BookProof_ChapterCyclicDirectSum_commute_starProjection_cfcHom
import Theorems.Thm_BookProof_ChapterCyclicDecomposition_invariant_cyclicSubspace
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
theorem solution (xi : H) (g : C(spectrum ℂ T, ℂ)) :
    Commute (cyclicSubspace T hT xi).starProjection (cfcHom hT g) := commute_starProjection_cfcHom T hT (invariant_cyclicSubspace T hT xi) g
