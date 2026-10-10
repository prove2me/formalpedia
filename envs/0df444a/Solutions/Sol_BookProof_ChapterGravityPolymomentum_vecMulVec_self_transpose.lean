-- Prove2me | solution 1 for BookProof.ChapterGravityPolymomentum.vecMulVec_self_transpose
-- status  : ACCEPTED   (prove)
-- author  : @leonardopedro
-- created : 2026-10-09T14:24:42.031676+00:00
-- url     : https://prove2.me/submissions/a0c75c6e-c17c-4432-9437-7b682fcf6994

-- Generated from ChapterGravityPolymomentum.lean — solution of BookProof.ChapterGravityPolymomentum.vecMulVec_self_transpose
import Mathlib
import Definitions.Def_ChapterGravityPolymomentum
import Definitions.Def_ChapterGravityProjector
open BookProof.ChapterGravityPolymomentum




open Matrix
open scoped BigOperators
open BookProof.ChapterGravityProjector

set_option maxHeartbeats 1000000 in
theorem solution (v : Fin 4 → ℝ) :
    (vecMulVec v v)ᵀ = vecMulVec v v := by

  ext a b; simp [vecMulVec_apply, Matrix.transpose_apply, mul_comm]
