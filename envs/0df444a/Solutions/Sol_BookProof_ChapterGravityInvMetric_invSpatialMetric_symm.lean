-- Prove2me | solution 1 for BookProof.ChapterGravityInvMetric.invSpatialMetric_symm
-- status  : ACCEPTED   (prove)
-- author  : @leonardopedro
-- created : 2026-10-09T07:50:59.725979+00:00
-- url     : https://prove2.me/submissions/2ca43233-8cfb-4e8d-bb9f-080b25930b33

-- Generated from ChapterGravityInvMetric.lean — solution of BookProof.ChapterGravityInvMetric.invSpatialMetric_symm
import Mathlib
import Definitions.Def_ChapterGravityInvMetric
open BookProof.ChapterGravityInvMetric




open Matrix
open scoped BigOperators
open BookProof.ChapterGravityProjector
open BookProof.ChapterGravityMetric

set_option maxHeartbeats 1000000 in
theorem solution (v : Fin 4 → ℝ) :
    (invSpatialMetric v)ᵀ = invSpatialMetric v := by

      ext i j; simp only [invSpatialMetric, transpose_apply, Matrix.add_apply, of_apply,
          mul_comm, add_left_inj]
      fin_cases i <;> fin_cases j <;> rfl
