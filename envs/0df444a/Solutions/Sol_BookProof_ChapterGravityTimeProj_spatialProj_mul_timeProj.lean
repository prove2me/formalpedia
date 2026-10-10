-- Prove2me | solution 1 for BookProof.ChapterGravityTimeProj.spatialProj_mul_timeProj
-- status  : ACCEPTED   (prove)
-- author  : @leonardopedro
-- created : 2026-10-09T14:33:37.380698+00:00
-- url     : https://prove2.me/submissions/68da9b6c-3d22-46f2-9af2-4988a424ab68

-- Generated from ChapterGravityTimeProj.lean — solution of BookProof.ChapterGravityTimeProj.spatialProj_mul_timeProj
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
    spatialProj v * timeProj v = 0 := by

  rw [ show timeProj v = 1 - spatialProj v from _ ];
  · simp [ mul_sub, spatialProj_idempotent v hv ];
  · exact eq_sub_of_add_eq' ( spatialProj_add_timeProj v )
