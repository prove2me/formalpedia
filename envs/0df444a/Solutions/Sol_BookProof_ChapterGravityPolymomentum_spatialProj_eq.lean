-- Prove2me | solution 1 for BookProof.ChapterGravityPolymomentum.spatialProj_eq
-- status  : ACCEPTED   (prove)
-- author  : @leonardopedro
-- created : 2026-10-09T08:44:12.213797+00:00
-- url     : https://prove2.me/submissions/20988c82-5d92-4844-b5f3-ca6b6ea05117

-- Generated from ChapterGravityPolymomentum.lean — solution of BookProof.ChapterGravityPolymomentum.spatialProj_eq
import Mathlib
import Definitions.Def_ChapterGravityPolymomentum
open BookProof.ChapterGravityPolymomentum




open Matrix
open scoped BigOperators
open BookProof.ChapterGravityProjector

set_option maxHeartbeats 1000000 in
theorem solution (v : Fin 4 → ℝ) : spatialProj v = 1 + vecMulVec v (lower v) := rfl
