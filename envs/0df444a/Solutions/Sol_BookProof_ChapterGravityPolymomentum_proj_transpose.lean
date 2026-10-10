-- Prove2me | solution 1 for BookProof.ChapterGravityPolymomentum.proj_transpose
-- status  : ACCEPTED   (prove)
-- author  : @leonardopedro
-- created : 2026-10-09T20:34:16.819972+00:00
-- url     : https://prove2.me/submissions/e37e4f66-c752-40e3-bb95-f1ab9fb29d2b

-- Generated from ChapterGravityPolymomentum.lean — solution of BookProof.ChapterGravityPolymomentum.proj_transpose
import Mathlib
import Definitions.Def_ChapterGravityPolymomentum
import Definitions.Def_ChapterElectroweakFieldStrength
import Definitions.Def_ChapterGravityProjector
open BookProof.ChapterGravityPolymomentum




open Matrix
open scoped BigOperators
open BookProof.ChapterGravityProjector

set_option maxHeartbeats 1000000 in
theorem solution (v : Fin 4 → ℝ) (M : Matrix (Fin 4) (Fin 4) ℝ) :
    BookProof.ChapterGravityPolymomentum.proj v (Mᵀ) = (BookProof.ChapterGravityPolymomentum.proj v M)ᵀ := by

  simp [BookProof.ChapterGravityPolymomentum.proj, Matrix.transpose_mul, Matrix.mul_assoc]
