-- Prove2me | solution 1 for BookProof.ChapterGravityProjector.spatialProj_mulVec_self
-- status  : ACCEPTED   (prove)
-- author  : @leonardopedro
-- created : 2026-10-09T14:30:10.263984+00:00
-- url     : https://prove2.me/submissions/c957fe60-57a8-4dd9-9838-bc2260158ffb

-- Generated from ChapterGravityProjector.lean — solution of BookProof.ChapterGravityProjector.spatialProj_mulVec_self
import Mathlib
import Definitions.Def_ChapterGravityProjector
open BookProof.ChapterGravityProjector




open Matrix
open scoped BigOperators

set_option maxHeartbeats 1000000 in
theorem solution (v : Fin 4 → ℝ) (hv : minkSq v = -1) :
    (spatialProj v).mulVec v = 0 := by

  ext a;
  simp only [mulVec, dotProduct, spatialProj, Matrix.add_apply, Matrix.of_apply, Pi.zero_apply];
  simp_all only [minkSq, lower, add_mul, mul_assoc, Finset.sum_add_distrib];
  simp_all only [Matrix.one_apply, mul_comm, mul_ite, mul_one, mul_zero, Finset.sum_ite_eq,
      Finset.mem_univ, ↓reduceIte];
  rw [← Finset.mul_sum, hv]; ring
