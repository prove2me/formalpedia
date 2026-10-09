-- Prove2me | solution 1 for BookProof.ChapterGravityPolymomentum.proj_sub
-- status  : ACCEPTED   (prove)
-- author  : @leonardopedro
-- created : 2026-10-09T08:45:04.274241+00:00
-- url     : https://prove2.me/submissions/375634bf-acbf-4134-b21e-4e865e50fe85

-- Generated from ChapterGravityPolymomentum.lean — solution of BookProof.ChapterGravityPolymomentum.proj_sub
import Mathlib
import Definitions.Def_ChapterGravityPolymomentum
open BookProof.ChapterGravityPolymomentum




open Matrix
open scoped BigOperators
open BookProof.ChapterGravityProjector

set_option maxHeartbeats 1000000 in
theorem solution (v : Fin 4 → ℝ) (M N : Matrix (Fin 4) (Fin 4) ℝ) :
    proj v (M - N) = proj v M - proj v N := by

  simp [proj, Matrix.mul_sub, Matrix.sub_mul]
