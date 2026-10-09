-- Prove2me | solution 1 for BookProof.ChapterGravityPolymomentum.metric_transpose
-- status  : ACCEPTED   (prove)
-- author  : @leonardopedro
-- created : 2026-10-09T08:44:09.769038+00:00
-- url     : https://prove2.me/submissions/f6b9ed5d-7c62-44af-bd3a-ff23edcda5ba

-- Generated from ChapterGravityPolymomentum.lean — solution of BookProof.ChapterGravityPolymomentum.metric_transpose
import Mathlib
import Definitions.Def_ChapterGravityPolymomentum
open BookProof.ChapterGravityPolymomentum




open Matrix
open scoped BigOperators
open BookProof.ChapterGravityProjector

set_option maxHeartbeats 1000000 in
theorem solution : (metric : Matrix (Fin 4) (Fin 4) ℝ)ᵀ = metric := by

  ext a b
  by_cases h : a = b
  · subst h; rfl
  · simp [metric, Matrix.diagonal, Matrix.transpose_apply, h, Ne.symm h]
