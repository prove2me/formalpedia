-- Prove2me | solution 1 for BookProof.ChapterGravityInvMetric.metric_mul_metric
-- status  : ACCEPTED   (prove)
-- author  : @leonardopedro
-- created : 2026-10-09T07:50:58.69701+00:00
-- url     : https://prove2.me/submissions/e2d572f4-4b92-4674-8dca-5112341d4c50

-- Generated from ChapterGravityInvMetric.lean — solution of BookProof.ChapterGravityInvMetric.metric_mul_metric
import Mathlib
import Definitions.Def_ChapterGravityInvMetric
open BookProof.ChapterGravityInvMetric




open Matrix
open scoped BigOperators
open BookProof.ChapterGravityProjector
open BookProof.ChapterGravityMetric

set_option maxHeartbeats 1000000 in
theorem solution : metric * metric = 1 := by

  ext i j; fin_cases i <;> fin_cases j <;> simp [ metric ] ;
