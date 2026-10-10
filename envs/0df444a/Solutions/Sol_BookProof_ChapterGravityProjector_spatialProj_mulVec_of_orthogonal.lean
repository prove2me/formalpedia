-- Prove2me | solution 1 for BookProof.ChapterGravityProjector.spatialProj_mulVec_of_orthogonal
-- status  : ACCEPTED   (prove)
-- author  : @leonardopedro
-- created : 2026-10-09T14:30:46.752076+00:00
-- url     : https://prove2.me/submissions/5b089440-678b-447d-bb67-5aa7f071bd81

-- Generated from ChapterGravityProjector.lean — solution of BookProof.ChapterGravityProjector.spatialProj_mulVec_of_orthogonal
import Mathlib
import Definitions.Def_ChapterGravityProjector
open BookProof.ChapterGravityProjector




open Matrix
open scoped BigOperators

set_option maxHeartbeats 1000000 in
theorem solution (v x : Fin 4 → ℝ)
    (hx : ∑ a, lower v a * x a = 0) :
    (spatialProj v).mulVec x = x := by

  simp_all [ spatialProj, Matrix.mulVec, funext_iff ];
  simp_all [ Matrix.one_apply, dotProduct ];
  simp_all [ Finset.sum_add_distrib, add_mul ];
  simp_all [ mul_assoc, ← Finset.mul_sum _ _ _ ]
