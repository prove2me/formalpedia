-- Prove2me | solution 1 for BookProof.ChapterGravityPolymomentum.calP_eq
-- status  : ACCEPTED   (prove)
-- author  : @leonardopedro
-- created : 2026-10-09T14:26:02.231566+00:00
-- url     : https://prove2.me/submissions/d5ecd294-4d71-4c5f-a6ea-ccef9479f8f8

-- Generated from ChapterGravityPolymomentum.lean — solution of BookProof.ChapterGravityPolymomentum.calP_eq
import Mathlib
import Definitions.Def_ChapterGravityPolymomentum
import Theorems.Thm_BookProof_ChapterGravityPolymomentum_trace_metric_mul_spatialMetric
import Theorems.Thm_BookProof_ChapterGravityPolymomentum_trace_metric_mul_of_antisymm
import Theorems.Thm_BookProof_ChapterGravityPolymomentum_proj_polyMom
import Definitions.Def_ChapterElectroweakFieldStrength
import Definitions.Def_ChapterGravityProjector
open BookProof.ChapterGravityPolymomentum




open Matrix
open scoped BigOperators
open BookProof.ChapterGravityProjector
open BookProof.ChapterElectroweakFieldStrength

variable {e T : ℝ} {S Tc : Matrix (Fin 4) (Fin 4) ℝ} {u v : Fin 4 → ℝ}

set_option maxHeartbeats 1000000 in
theorem solution (hv : minkSq v = -1) (hS : IsSpatial v S) (hTc : IsSpatial v Tc)
    (hStraceless : (metric * S).trace = 0) (hTcanti : Tcᵀ = -Tc) :
    calP v (polyMom e T S Tc u v) = -4 * e * T := by

  have hp := proj_polyMom (e := e) (T := T) (u := u) hv hS hTc
  have htrTc : (metric * Tc).trace = 0 := trace_metric_mul_of_antisymm hTcanti
  have htrh := trace_metric_mul_spatialMetric v hv
  rw [calP, hp]
  simp only [Matrix.mul_smul, Matrix.mul_sub, Matrix.trace_smul, Matrix.trace_sub,
    smul_eq_mul, hStraceless, htrTc, htrh]
  ring
