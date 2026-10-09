-- Prove2me | solution 1 for BookProof.ChapterGravityMetric.spatialMetric_quadForm_nonneg
-- status  : ACCEPTED   (prove)
-- author  : @leonardopedro
-- created : 2026-10-09T07:52:35.67495+00:00
-- url     : https://prove2.me/submissions/09a3b9fd-08df-42ef-a84f-8f22a3b9c1f8

-- Generated from ChapterGravityMetric.lean — solution of BookProof.ChapterGravityMetric.spatialMetric_quadForm_nonneg
import Mathlib
import Definitions.Def_ChapterGravityMetric
import Theorems.Thm_BookProof_ChapterGravityMetric_reverse_cauchy_schwarz
open BookProof.ChapterGravityMetric




open Matrix
open scoped BigOperators
open BookProof.ChapterGravityProjector

set_option maxHeartbeats 1000000 in
theorem solution (v x : Fin 4 → ℝ) (hv : minkSq v = -1) :
    0 ≤ x ⬝ᵥ ((spatialMetric v).mulVec x) := by

      convert reverse_cauchy_schwarz v x hv using 1;
      unfold spatialMetric minkSq;
      unfold lower; unfold metric; simp [ Fin.sum_univ_four, Matrix.mulVec, dotProduct ] ; ring;
