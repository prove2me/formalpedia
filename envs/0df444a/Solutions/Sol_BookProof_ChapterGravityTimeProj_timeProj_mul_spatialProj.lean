-- Prove2me | solution 1 for BookProof.ChapterGravityTimeProj.timeProj_mul_spatialProj
-- status  : ACCEPTED   (prove)
-- author  : @leonardopedro
-- created : 2026-10-09T14:33:59.545924+00:00
-- url     : https://prove2.me/submissions/d1aaa2b5-ed12-4a13-a5db-98e752e6fa5b

-- Generated from ChapterGravityTimeProj.lean — solution of BookProof.ChapterGravityTimeProj.timeProj_mul_spatialProj
import Mathlib
import Definitions.Def_ChapterGravityTimeProj
import Theorems.Thm_BookProof_ChapterGravityTimeProj_spatialProj_add_timeProj
import Theorems.Thm_BookProof_ChapterGravityProjector_spatialProj_idempotent
import Definitions.Def_ChapterGravityProjector
open BookProof.ChapterGravityTimeProj




open Matrix
open scoped BigOperators
open BookProof.ChapterGravityProjector

set_option maxHeartbeats 1000000 in
theorem solution (v : Fin 4 → ℝ) (hv : minkSq v = -1) :
    timeProj v * spatialProj v = 0 := by

  -- Since timeProj = 1 - spatialProj (from spatialProj_add_timeProj), we can rewrite the goal using
  -- this equality.
  have h_timeProj : timeProj v = 1 - spatialProj v := by
    exact eq_sub_of_add_eq' ( spatialProj_add_timeProj v );
  simp [ h_timeProj, sub_mul,spatialProj_idempotent v hv ]
