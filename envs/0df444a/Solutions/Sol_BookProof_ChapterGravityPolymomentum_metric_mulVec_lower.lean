-- Prove2me | solution 1 for BookProof.ChapterGravityPolymomentum.metric_mulVec_lower
-- status  : ACCEPTED   (prove)
-- author  : @leonardopedro
-- created : 2026-10-09T08:44:10.8473+00:00
-- url     : https://prove2.me/submissions/94f16fbe-2e73-4e4f-ad50-d46dfed15c2b

-- Generated from ChapterGravityPolymomentum.lean — solution of BookProof.ChapterGravityPolymomentum.metric_mulVec_lower
import Mathlib
import Definitions.Def_ChapterGravityPolymomentum
import Theorems.Thm_BookProof_ChapterGravityPolymomentum_metric_mul_metric
open BookProof.ChapterGravityPolymomentum




open Matrix
open scoped BigOperators
open BookProof.ChapterGravityProjector

set_option maxHeartbeats 1000000 in
theorem solution (v : Fin 4 → ℝ) : metric.mulVec (lower v) = v := by

  calc metric.mulVec (lower v) = (metric * metric).mulVec v := by
        simp [lower, Matrix.mulVec_mulVec]
    _ = v := by simp [metric_mul_metric]
