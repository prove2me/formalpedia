-- Prove2me | solution 1 for BookProof.ChapterGravityProjector.spatialProj_idempotent
-- status  : ACCEPTED   (prove)
-- author  : @leonardopedro
-- created : 2026-10-09T14:30:22.061627+00:00
-- url     : https://prove2.me/submissions/912103c9-2112-4be9-8cc1-6ad70e45edc2

-- Generated from ChapterGravityProjector.lean — solution of BookProof.ChapterGravityProjector.spatialProj_idempotent
import Mathlib
import Definitions.Def_ChapterGravityProjector
open BookProof.ChapterGravityProjector




open Matrix
open scoped BigOperators

set_option maxHeartbeats 1000000 in
theorem solution (v : Fin 4 → ℝ) (hv : minkSq v = -1) :
    spatialProj v * spatialProj v = spatialProj v := by

  -- M*M at (a,b) = ∑_c (v a * lower v c)(v c * lower v b) = v a * lower v b * (∑_c lower v c * v c)
  have hM2 : ∀ a b, (∑ c, (v a * lower v c) * (v c * lower v b)) = -(v a * lower v b) := by
    simp_all [ minkSq, lower, Fin.sum_univ_four ];
    grind;
  ext a b;    simp [ *, Matrix.mul_apply ] ;    ring;
  simp_all [ spatialProj ] ; ring;
  simp_all [ Finset.sum_add_distrib, mul_assoc, Matrix.one_apply ] ; ring
