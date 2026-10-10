-- Prove2me | solution 1 for BookProof.ChapterGravityPolymomentum.spatialMetric_transpose
-- status  : ACCEPTED   (prove)
-- author  : @leonardopedro
-- created : 2026-10-09T14:24:53.61898+00:00
-- url     : https://prove2.me/submissions/d798f492-dfda-41d1-aaa2-8545f2261c71

-- Generated from ChapterGravityPolymomentum.lean — solution of BookProof.ChapterGravityPolymomentum.spatialMetric_transpose
import Mathlib
import Definitions.Def_ChapterGravityPolymomentum
import Theorems.Thm_BookProof_ChapterGravityPolymomentum_metric_transpose
import Theorems.Thm_BookProof_ChapterGravityPolymomentum_vecMulVec_self_transpose
import Definitions.Def_ChapterGravityProjector
open BookProof.ChapterGravityPolymomentum




open Matrix
open scoped BigOperators
open BookProof.ChapterGravityProjector

set_option maxHeartbeats 1000000 in
theorem solution (v : Fin 4 → ℝ) :
    (metric + vecMulVec v v)ᵀ = metric + vecMulVec v v := by

  rw [Matrix.transpose_add, metric_transpose, vecMulVec_self_transpose]
