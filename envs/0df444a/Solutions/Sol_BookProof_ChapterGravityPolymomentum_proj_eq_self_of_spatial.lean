-- Prove2me | solution 1 for BookProof.ChapterGravityPolymomentum.proj_eq_self_of_spatial
-- status  : ACCEPTED   (prove)
-- author  : @leonardopedro
-- created : 2026-10-09T20:35:16.184669+00:00
-- url     : https://prove2.me/submissions/0444f3ef-7205-4875-af9f-b6f9ca8af97f

-- Generated from ChapterGravityPolymomentum.lean — solution of BookProof.ChapterGravityPolymomentum.proj_eq_self_of_spatial
import Mathlib
import Definitions.Def_ChapterGravityPolymomentum
import Theorems.Thm_BookProof_ChapterGravityPolymomentum_spatialProj_mul
import Theorems.Thm_BookProof_ChapterGravityPolymomentum_mul_spatialProj_transpose
import Definitions.Def_ChapterElectroweakFieldStrength
import Definitions.Def_ChapterGravityProjector
open BookProof.ChapterGravityPolymomentum




open Matrix
open scoped BigOperators
open BookProof.ChapterGravityProjector

set_option maxHeartbeats 1000000 in
theorem solution (v : Fin 4 → ℝ) {M : Matrix (Fin 4) (Fin 4) ℝ}
    (h : IsSpatial v M) : BookProof.ChapterGravityPolymomentum.proj v M = M := by

  rw [BookProof.ChapterGravityPolymomentum.proj, spatialProj_mul, h.left]
  simp [mul_spatialProj_transpose, h.right]
