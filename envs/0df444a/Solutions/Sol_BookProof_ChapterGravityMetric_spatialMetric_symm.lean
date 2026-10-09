-- Prove2me | solution 1 for BookProof.ChapterGravityMetric.spatialMetric_symm
-- status  : ACCEPTED   (prove)
-- author  : @leonardopedro
-- created : 2026-10-09T07:52:07.484003+00:00
-- url     : https://prove2.me/submissions/1e073812-de8b-4c15-a738-488980bff665

-- Generated from ChapterGravityMetric.lean — solution of BookProof.ChapterGravityMetric.spatialMetric_symm
import Mathlib
import Definitions.Def_ChapterGravityMetric
open BookProof.ChapterGravityMetric




open Matrix
open scoped BigOperators
open BookProof.ChapterGravityProjector

set_option maxHeartbeats 1000000 in
theorem solution (v : Fin 4 → ℝ) :
    (spatialMetric v)ᵀ = spatialMetric v := by

      unfold spatialMetric; ext i j; simp only [lower, transpose_apply, Matrix.add_apply, of_apply,
          mul_comm, add_left_inj] ;
      unfold metric; fin_cases i <;> fin_cases j <;> rfl;
