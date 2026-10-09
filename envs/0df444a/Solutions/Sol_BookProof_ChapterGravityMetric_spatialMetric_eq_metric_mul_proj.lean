-- Prove2me | solution 1 for BookProof.ChapterGravityMetric.spatialMetric_eq_metric_mul_proj
-- status  : ACCEPTED   (prove)
-- author  : @leonardopedro
-- created : 2026-10-09T07:52:20.457994+00:00
-- url     : https://prove2.me/submissions/026de828-65e1-428d-9047-e06597db59f9

-- Generated from ChapterGravityMetric.lean — solution of BookProof.ChapterGravityMetric.spatialMetric_eq_metric_mul_proj
import Mathlib
import Definitions.Def_ChapterGravityMetric
open BookProof.ChapterGravityMetric




open Matrix
open scoped BigOperators
open BookProof.ChapterGravityProjector

set_option maxHeartbeats 1000000 in
theorem solution (v : Fin 4 → ℝ) :
    spatialMetric v = metric * spatialProj v := by

      ext a b; simp only [spatialMetric, Matrix.add_apply, of_apply, spatialProj, mul_apply,
          Fin.sum_univ_four, Fin.isValue] ; ring;
      simp only [metric, Fin.isValue, lower, mulVec, dotProduct, Fin.sum_univ_four] ; ring;
      fin_cases a <;> fin_cases b <;> simp [ Matrix.one_apply ]; all_goals ring
