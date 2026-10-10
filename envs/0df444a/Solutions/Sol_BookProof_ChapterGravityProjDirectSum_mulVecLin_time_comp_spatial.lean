-- Prove2me | solution 1 for BookProof.ChapterGravityProjDirectSum.mulVecLin_time_comp_spatial
-- status  : ACCEPTED   (prove)
-- author  : @leonardopedro
-- created : 2026-10-09T14:29:01.524479+00:00
-- url     : https://prove2.me/submissions/1e7978d6-0453-4f4c-8861-37a63daacf2a

-- Generated from ChapterGravityProjDirectSum.lean — solution of BookProof.ChapterGravityProjDirectSum.mulVecLin_time_comp_spatial
import Mathlib
import Definitions.Def_ChapterGravityProjDirectSum
import Theorems.Thm_BookProof_ChapterGravityTimeProj_timeProj_mul_spatialProj
import Definitions.Def_ChapterGravityProjector
import Definitions.Def_ChapterGravityTimeProj
open BookProof.ChapterGravityProjDirectSum



open Matrix


open BookProof.ChapterGravityProjector
open BookProof.ChapterGravityTimeProj

set_option maxHeartbeats 1000000 in
theorem solution (v : Fin 4 → ℝ) (hv : minkSq v = -1) :
    (timeProj v).mulVecLin.comp (spatialProj v).mulVecLin = 0 := by

  rw [← Matrix.mulVecLin_mul, timeProj_mul_spatialProj v hv, Matrix.mulVecLin_zero]
