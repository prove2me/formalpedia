-- Prove2me | solution 1 for BookProof.ChapterGravityPolymomentum.proj_add
-- status  : ACCEPTED   (prove)
-- author  : @leonardopedro
-- created : 2026-10-09T08:44:28.445375+00:00
-- url     : https://prove2.me/submissions/4e971dba-821e-4600-b804-4015c92939df

-- Generated from ChapterGravityPolymomentum.lean — solution of BookProof.ChapterGravityPolymomentum.proj_add
import Mathlib
import Definitions.Def_ChapterGravityPolymomentum
open BookProof.ChapterGravityPolymomentum




open Matrix
open scoped BigOperators
open BookProof.ChapterGravityProjector

set_option maxHeartbeats 1000000 in
theorem solution (v : Fin 4 → ℝ) (M N : Matrix (Fin 4) (Fin 4) ℝ) :
    proj v (M + N) = proj v M + proj v N := by

  simp [proj, Matrix.mul_add, Matrix.add_mul]
