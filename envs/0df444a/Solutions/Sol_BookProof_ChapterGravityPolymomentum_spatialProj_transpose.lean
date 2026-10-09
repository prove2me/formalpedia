-- Prove2me | solution 1 for BookProof.ChapterGravityPolymomentum.spatialProj_transpose
-- status  : ACCEPTED   (prove)
-- author  : @leonardopedro
-- created : 2026-10-09T08:44:13.186365+00:00
-- url     : https://prove2.me/submissions/9555f2bd-3e48-4552-91c3-8ebcacbf7bb2

-- Generated from ChapterGravityPolymomentum.lean — solution of BookProof.ChapterGravityPolymomentum.spatialProj_transpose
import Mathlib
import Definitions.Def_ChapterGravityPolymomentum
open BookProof.ChapterGravityPolymomentum




open Matrix
open scoped BigOperators
open BookProof.ChapterGravityProjector

set_option maxHeartbeats 1000000 in
theorem solution (v : Fin 4 → ℝ) :
    (spatialProj v)ᵀ = 1 + vecMulVec (lower v) v := by

  ext a b
  simp [spatialProj, vecMulVec_apply, Matrix.transpose_apply, Matrix.one_apply, eq_comm, mul_comm]
