-- Prove2me | solution 1 for BookProof.ChapterGravityPolymomentum.metric_mul_metric
-- status  : ACCEPTED   (prove)
-- author  : @leonardopedro
-- created : 2026-10-09T08:44:08.665703+00:00
-- url     : https://prove2.me/submissions/27950b90-e1cb-423d-98c9-c5a9e5ab403d

-- Generated from ChapterGravityPolymomentum.lean — solution of BookProof.ChapterGravityPolymomentum.metric_mul_metric
import Mathlib
import Definitions.Def_ChapterGravityPolymomentum
open BookProof.ChapterGravityPolymomentum




open Matrix
open scoped BigOperators
open BookProof.ChapterGravityProjector

set_option maxHeartbeats 1000000 in
theorem solution : metric * metric = (1 : Matrix (Fin 4) (Fin 4) ℝ) := by

  ext a b
  fin_cases a <;> fin_cases b <;>
    simp [metric, Matrix.mul_apply, Matrix.diagonal]
