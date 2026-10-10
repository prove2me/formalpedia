-- Prove2me | solution 1 for BookProof.ChapterGravityPolymomentum.proj_vecMulVec_right
-- status  : ACCEPTED   (prove)
-- author  : @leonardopedro
-- created : 2026-10-09T20:36:15.719553+00:00
-- url     : https://prove2.me/submissions/ee232019-9cf1-4f53-b9a9-070245214440

-- Generated from ChapterGravityPolymomentum.lean — solution of BookProof.ChapterGravityPolymomentum.proj_vecMulVec_right
import Mathlib
import Definitions.Def_ChapterGravityPolymomentum
import Theorems.Thm_BookProof_ChapterGravityPolymomentum_vecMulVec_mul
import Theorems.Thm_BookProof_ChapterGravityPolymomentum_mul_vecMulVec
import Theorems.Thm_BookProof_ChapterGravityProjector_spatialProj_mulVec_self
import Definitions.Def_ChapterElectroweakFieldStrength
import Definitions.Def_ChapterGravityProjector
open BookProof.ChapterGravityPolymomentum




open Matrix
open scoped BigOperators
open BookProof.ChapterGravityProjector

set_option maxHeartbeats 1000000 in
theorem solution (v : Fin 4 → ℝ) (hv : minkSq v = -1) (u : Fin 4 → ℝ) :
    BookProof.ChapterGravityPolymomentum.proj v (vecMulVec u v) = 0 := by

  have hXv : (spatialProj v).mulVec v = 0 := spatialProj_mulVec_self v hv
  have h1 : (spatialProj v)ᵀ.vecMul v = 0 := by
    rw [Matrix.vecMul_transpose, hXv]
  rw [BookProof.ChapterGravityPolymomentum.proj, mul_vecMulVec, vecMulVec_mul, h1]
  simp
