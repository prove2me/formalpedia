-- Prove2me | solution 1 for BookProof.ChapterGravityPolymomentum.trace_metric_mul_of_antisymm
-- status  : ACCEPTED   (prove)
-- author  : @leonardopedro
-- created : 2026-10-09T14:25:16.477129+00:00
-- url     : https://prove2.me/submissions/2e98b13b-ed12-4cec-80eb-ae68381b249e

-- Generated from ChapterGravityPolymomentum.lean — solution of BookProof.ChapterGravityPolymomentum.trace_metric_mul_of_antisymm
import Mathlib
import Definitions.Def_ChapterGravityPolymomentum
import Theorems.Thm_BookProof_ChapterGravityPolymomentum_metric_transpose
import Definitions.Def_ChapterGravityProjector
open BookProof.ChapterGravityPolymomentum




open Matrix
open scoped BigOperators
open BookProof.ChapterGravityProjector

set_option maxHeartbeats 1000000 in
theorem solution {M : Matrix (Fin 4) (Fin 4) ℝ} (hM : Mᵀ = -M) :
    (metric * M).trace = 0 := by

  have h1 : (metric * M).trace = ((metric * M)ᵀ).trace := (Matrix.trace_transpose _).symm
  have h2 : ((metric * M)ᵀ).trace = (Mᵀ * metric).trace := by
    rw [Matrix.transpose_mul, metric_transpose]
  have h3 : (Mᵀ * metric).trace = -(metric * M).trace := by
    rw [hM, Matrix.neg_mul, Matrix.trace_neg, Matrix.trace_mul_comm]
  have := h1.trans (h2.trans h3)
  linarith
