-- Prove2me | solution 1 for BookProof.ChapterGravityProjDirectSum.mulVecLin_spatial_comp_time
-- status  : ACCEPTED   (prove)
-- author  : @leonardopedro
-- created : 2026-10-09T14:28:39.923562+00:00
-- url     : https://prove2.me/submissions/5d25562f-7732-468f-ac91-287618b6b60c

-- Generated from ChapterGravityProjDirectSum.lean — solution of BookProof.ChapterGravityProjDirectSum.mulVecLin_spatial_comp_time
import Mathlib
import Definitions.Def_ChapterGravityProjDirectSum
import Theorems.Thm_BookProof_ChapterGravityTimeProj_spatialProj_mul_timeProj
import Definitions.Def_ChapterGravityProjector
import Definitions.Def_ChapterGravityTimeProj
open BookProof.ChapterGravityProjDirectSum



open Matrix


open BookProof.ChapterGravityProjector
open BookProof.ChapterGravityTimeProj

set_option maxHeartbeats 1000000 in
theorem solution (v : Fin 4 → ℝ) (hv : minkSq v = -1) :
    (spatialProj v).mulVecLin.comp (timeProj v).mulVecLin = 0 := by

  rw [← Matrix.mulVecLin_mul, spatialProj_mul_timeProj v hv, Matrix.mulVecLin_zero]
