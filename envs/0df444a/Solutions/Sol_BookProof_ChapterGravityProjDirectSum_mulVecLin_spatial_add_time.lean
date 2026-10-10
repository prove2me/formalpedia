-- Prove2me | solution 1 for BookProof.ChapterGravityProjDirectSum.mulVecLin_spatial_add_time
-- status  : ACCEPTED   (prove)
-- author  : @leonardopedro
-- created : 2026-10-09T14:28:17.817727+00:00
-- url     : https://prove2.me/submissions/4e4a53a1-8acd-4193-9a52-d141674fa3f1

-- Generated from ChapterGravityProjDirectSum.lean — solution of BookProof.ChapterGravityProjDirectSum.mulVecLin_spatial_add_time
import Mathlib
import Definitions.Def_ChapterGravityProjDirectSum
import Theorems.Thm_BookProof_ChapterGravityTimeProj_spatialProj_add_timeProj
import Definitions.Def_ChapterGravityProjector
import Definitions.Def_ChapterGravityTimeProj
open BookProof.ChapterGravityProjDirectSum



open Matrix


open BookProof.ChapterGravityProjector
open BookProof.ChapterGravityTimeProj

set_option maxHeartbeats 1000000 in
theorem solution (v : Fin 4 → ℝ) :
    (spatialProj v).mulVecLin + (timeProj v).mulVecLin = LinearMap.id := by

  rw [← Matrix.mulVecLin_add, spatialProj_add_timeProj, Matrix.mulVecLin_one]
