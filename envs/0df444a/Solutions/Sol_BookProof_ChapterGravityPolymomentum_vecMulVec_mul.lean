-- Prove2me | solution 1 for BookProof.ChapterGravityPolymomentum.vecMulVec_mul
-- status  : ACCEPTED   (prove)
-- author  : @leonardopedro
-- created : 2026-10-09T07:53:01.400988+00:00
-- url     : https://prove2.me/submissions/a135af42-fd8f-4207-a4c0-33db96a90f7d

-- Generated from ChapterGravityPolymomentum.lean — solution of BookProof.ChapterGravityPolymomentum.vecMulVec_mul
import Mathlib
import Definitions.Def_ChapterGravityPolymomentum
open BookProof.ChapterGravityPolymomentum




open Matrix
open scoped BigOperators
open BookProof.ChapterGravityProjector

set_option maxHeartbeats 1000000 in
theorem solution (w u : Fin 4 → ℝ) (M : Matrix (Fin 4) (Fin 4) ℝ) :
    vecMulVec w u * M = vecMulVec w (M.vecMul u) := by

  ext a b
  simp [Matrix.mul_apply, vecMulVec_apply, Matrix.vecMul, dotProduct, Finset.mul_sum, mul_assoc]
