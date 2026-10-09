-- Prove2me | solution 1 for BookProof.ChapterGravityMetric.spatialMetric_mulVec_self
-- status  : ACCEPTED   (prove)
-- author  : @leonardopedro
-- created : 2026-10-09T07:52:33.497981+00:00
-- url     : https://prove2.me/submissions/829adff2-e6f6-4f6e-9e4d-d78dc6e2bc95

-- Generated from ChapterGravityMetric.lean — solution of BookProof.ChapterGravityMetric.spatialMetric_mulVec_self
import Mathlib
import Definitions.Def_ChapterGravityMetric
open BookProof.ChapterGravityMetric




open Matrix
open scoped BigOperators
open BookProof.ChapterGravityProjector

set_option maxHeartbeats 1000000 in
theorem solution (v : Fin 4 → ℝ) (hv : minkSq v = -1) :
    (spatialMetric v).mulVec v = 0 := by

      unfold spatialMetric minkSq at *;
      unfold lower metric at *;
      ext i; simp_all [ Matrix.mulVec, dotProduct, Fin.sum_univ_four ] ;
      grind
