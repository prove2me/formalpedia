-- Prove2me | solution 1 for BookProof.ChapterGravityTimeProj.timeProj_mulVec_self
-- status  : ACCEPTED   (prove)
-- author  : @leonardopedro
-- created : 2026-10-09T14:33:15.397388+00:00
-- url     : https://prove2.me/submissions/688c7fba-c108-4e24-997f-c5990c69c6ec

-- Generated from ChapterGravityTimeProj.lean — solution of BookProof.ChapterGravityTimeProj.timeProj_mulVec_self
import Mathlib
import Definitions.Def_ChapterGravityTimeProj
import Definitions.Def_ChapterGravityProjector
open BookProof.ChapterGravityTimeProj




open Matrix
open scoped BigOperators
open BookProof.ChapterGravityProjector

set_option maxHeartbeats 1000000 in
theorem solution (v : Fin 4 → ℝ) (hv : minkSq v = -1) :
    (timeProj v).mulVec v = v := by

  ext a;
  simp [minkSq, timeProj] at hv ⊢;
  simp_all [ Matrix.mulVec, dotProduct, Fin.sum_univ_four ];
  linear_combination -hv * v a
