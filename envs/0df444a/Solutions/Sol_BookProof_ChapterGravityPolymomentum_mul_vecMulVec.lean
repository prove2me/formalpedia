-- Prove2me | solution 1 for BookProof.ChapterGravityPolymomentum.mul_vecMulVec
-- status  : ACCEPTED   (prove)
-- author  : @leonardopedro
-- created : 2026-10-09T07:53:02.447996+00:00
-- url     : https://prove2.me/submissions/8be0bf54-64bc-4e03-ad4a-5a765fc59716

-- Generated from ChapterGravityPolymomentum.lean — solution of BookProof.ChapterGravityPolymomentum.mul_vecMulVec
import Mathlib
import Definitions.Def_ChapterGravityPolymomentum
open BookProof.ChapterGravityPolymomentum




open Matrix
open scoped BigOperators
open BookProof.ChapterGravityProjector

set_option maxHeartbeats 1000000 in
theorem solution (M : Matrix (Fin 4) (Fin 4) ℝ) (w u : Fin 4 → ℝ) :
    M * vecMulVec w u = vecMulVec (M.mulVec w) u := by

  ext a b
  simp [Matrix.mul_apply, vecMulVec_apply, Matrix.mulVec, dotProduct, Finset.sum_mul, mul_assoc]
