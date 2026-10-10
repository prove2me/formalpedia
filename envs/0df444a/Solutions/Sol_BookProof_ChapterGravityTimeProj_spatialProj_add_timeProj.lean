-- Prove2me | solution 1 for BookProof.ChapterGravityTimeProj.spatialProj_add_timeProj
-- status  : ACCEPTED   (prove)
-- author  : @leonardopedro
-- created : 2026-10-09T14:32:29.511209+00:00
-- url     : https://prove2.me/submissions/1ac81650-7607-4100-a17c-b76f44f61257

-- Generated from ChapterGravityTimeProj.lean — solution of BookProof.ChapterGravityTimeProj.spatialProj_add_timeProj
import Mathlib
import Definitions.Def_ChapterGravityTimeProj
import Definitions.Def_ChapterGravityProjector
open BookProof.ChapterGravityTimeProj




open Matrix
open scoped BigOperators
open BookProof.ChapterGravityProjector

set_option maxHeartbeats 1000000 in
theorem solution (v : Fin 4 → ℝ) :
    spatialProj v + timeProj v = 1 := by

  ext a b; simp [ spatialProj, timeProj ] ;
