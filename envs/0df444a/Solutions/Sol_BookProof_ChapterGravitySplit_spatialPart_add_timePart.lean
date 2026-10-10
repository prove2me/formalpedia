-- Prove2me | solution 1 for BookProof.ChapterGravitySplit.spatialPart_add_timePart
-- status  : ACCEPTED   (prove)
-- author  : @leonardopedro
-- created : 2026-10-09T14:31:42.664821+00:00
-- url     : https://prove2.me/submissions/4dfb7399-3efc-49ae-a8ec-b68a815ab7fb

-- Generated from ChapterGravitySplit.lean — solution of BookProof.ChapterGravitySplit.spatialPart_add_timePart
import Mathlib
import Definitions.Def_ChapterGravitySplit
import Theorems.Thm_BookProof_ChapterGravityTimeProj_spatialProj_add_timeProj
import Definitions.Def_ChapterGravityProjector
import Definitions.Def_ChapterGravityTimeProj
open BookProof.ChapterGravitySplit




open Matrix
open scoped BigOperators
open BookProof.ChapterGravityProjector
open BookProof.ChapterGravityTimeProj

set_option maxHeartbeats 1000000 in
theorem solution (v x : Fin 4 → ℝ) :
    spatialPart v x + timePart v x = x := by

  unfold spatialPart timePart;
  rw [ ← Matrix.add_mulVec, BookProof.ChapterGravityTimeProj.spatialProj_add_timeProj,
      Matrix.one_mulVec ]
