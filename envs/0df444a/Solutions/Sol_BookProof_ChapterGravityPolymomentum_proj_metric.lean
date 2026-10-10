-- Prove2me | solution 1 for BookProof.ChapterGravityPolymomentum.proj_metric
-- status  : ACCEPTED   (prove)
-- author  : @leonardopedro
-- created : 2026-10-09T20:37:11.049499+00:00
-- url     : https://prove2.me/submissions/272a2d71-d3cf-4d48-82c4-6945f008ae85

-- Generated from ChapterGravityPolymomentum.lean — solution of BookProof.ChapterGravityPolymomentum.proj_metric
import Mathlib
import Definitions.Def_ChapterGravityPolymomentum
import Theorems.Thm_BookProof_ChapterGravityPolymomentum_vecMulVec_mul
import Theorems.Thm_BookProof_ChapterGravityPolymomentum_metric_transpose
import Theorems.Thm_BookProof_ChapterGravityPolymomentum_metric_mulVec_lower
import Theorems.Thm_BookProof_ChapterGravityPolymomentum_spatialProj_mul
import Theorems.Thm_BookProof_ChapterGravityPolymomentum_mul_spatialProj_transpose
import Theorems.Thm_BookProof_ChapterGravityProjector_spatialProj_mulVec_self
import Definitions.Def_ChapterElectroweakFieldStrength
import Definitions.Def_ChapterGravityProjector
open BookProof.ChapterGravityPolymomentum




open Matrix
open scoped BigOperators
open BookProof.ChapterGravityProjector

set_option maxHeartbeats 1000000 in
theorem solution (v : Fin 4 → ℝ) (hv : minkSq v = -1) :
    BookProof.ChapterGravityPolymomentum.proj v metric = metric + vecMulVec v v := by

  have hml : metric.mulVec (lower v) = v := metric_mulVec_lower v
  have hvm : metric.vecMul (lower v) = v := by
    have h := Matrix.vecMul_transpose (metric : Matrix (Fin 4) (Fin 4) ℝ) (lower v)
    rwa [metric_transpose, hml] at h
  have hXv : (spatialProj v).mulVec v = 0 := spatialProj_mulVec_self v hv
  have h1 : (spatialProj v)ᵀ.vecMul v = 0 := by rw [Matrix.vecMul_transpose, hXv]
  have h2 : vecMulVec v v * (spatialProj v)ᵀ = 0 := by
    rw [vecMulVec_mul, h1]; simp
  calc BookProof.ChapterGravityPolymomentum.proj v metric = (metric + vecMulVec v v) * (spatialProj v)ᵀ := by
        rw [BookProof.ChapterGravityPolymomentum.proj, spatialProj_mul, hvm]
    _ = metric + vecMulVec v v := by
        rw [Matrix.add_mul, h2, mul_spatialProj_transpose, hml, add_zero]
