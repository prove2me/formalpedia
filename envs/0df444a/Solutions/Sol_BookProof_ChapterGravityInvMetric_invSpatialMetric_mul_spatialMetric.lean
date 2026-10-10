-- Prove2me | solution 1 for BookProof.ChapterGravityInvMetric.invSpatialMetric_mul_spatialMetric
-- status  : ACCEPTED   (prove)
-- author  : @leonardopedro
-- created : 2026-10-09T14:22:48.350746+00:00
-- url     : https://prove2.me/submissions/41c64d7d-43e0-454c-85f3-0f688212f175

-- Generated from ChapterGravityInvMetric.lean — solution of BookProof.ChapterGravityInvMetric.invSpatialMetric_mul_spatialMetric
import Mathlib
import Definitions.Def_ChapterGravityInvMetric
import Theorems.Thm_BookProof_ChapterGravityInvMetric_metric_mul_metric
import Theorems.Thm_BookProof_ChapterGravityMetric_spatialMetric_eq_metric_mul_proj
import Theorems.Thm_BookProof_ChapterGravityProjector_spatialProj_idempotent
import Definitions.Def_ChapterGravityMetric
import Definitions.Def_ChapterGravityProjector
open BookProof.ChapterGravityInvMetric




open Matrix
open scoped BigOperators
open BookProof.ChapterGravityProjector
open BookProof.ChapterGravityMetric

set_option maxHeartbeats 1000000 in
theorem solution (v : Fin 4 → ℝ) (hv : minkSq v = -1) :
    invSpatialMetric v * spatialMetric v = spatialProj v := by

      have msym : ∀ i j : Fin 4, metric i j = metric j i := by
        intro i j
        by_cases h : i = j
        · simp [metric, h]
        · simp [metric, h, eq_comm]
      have h1 : invSpatialMetric v * metric = spatialProj v := by
        unfold invSpatialMetric spatialProj
        rw [add_mul, metric_mul_metric]
        congr 1
        ext a b
        simp only [of_apply, mul_apply, mulVec, dotProduct, lower, mul_assoc]
        rw [Finset.mul_sum]
        exact Finset.sum_congr rfl fun k _ => by
          rw [msym b k, mul_comm (v k) (metric k b)]
      rw [spatialMetric_eq_metric_mul_proj, ← mul_assoc, h1,
        spatialProj_idempotent v hv]
