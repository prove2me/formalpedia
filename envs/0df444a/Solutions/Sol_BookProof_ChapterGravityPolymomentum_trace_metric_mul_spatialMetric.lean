-- Prove2me | solution 1 for BookProof.ChapterGravityPolymomentum.trace_metric_mul_spatialMetric
-- status  : ACCEPTED   (prove)
-- author  : @leonardopedro
-- created : 2026-10-09T14:24:54.71004+00:00
-- url     : https://prove2.me/submissions/72033d2c-669b-4ea1-af24-b365e023ef9e

-- Generated from ChapterGravityPolymomentum.lean — solution of BookProof.ChapterGravityPolymomentum.trace_metric_mul_spatialMetric
import Mathlib
import Definitions.Def_ChapterGravityPolymomentum
import Theorems.Thm_BookProof_ChapterGravityPolymomentum_mul_vecMulVec
import Theorems.Thm_BookProof_ChapterGravityPolymomentum_trace_vecMulVec
import Theorems.Thm_BookProof_ChapterGravityPolymomentum_metric_mul_metric
import Definitions.Def_ChapterGravityProjector
open BookProof.ChapterGravityPolymomentum




open Matrix
open scoped BigOperators
open BookProof.ChapterGravityProjector

set_option maxHeartbeats 1000000 in
theorem solution (v : Fin 4 → ℝ) (hv : minkSq v = -1) :
    (metric * (metric + vecMulVec v v)).trace = 3 := by

  have h1 : metric * (metric + vecMulVec v v) = 1 + vecMulVec (metric.mulVec v) v := by
    rw [Matrix.mul_add, metric_mul_metric, mul_vecMulVec]
  have h2 : (vecMulVec (metric.mulVec v) v).trace = -1 := by
    rw [trace_vecMulVec]
    have : ∑ a, metric.mulVec v a * v a = minkSq v := by
      simp [minkSq, lower, mul_comm]
    rw [this, hv]
  rw [h1, Matrix.trace_add, h2]
  simp [Matrix.trace_one]
  norm_num
