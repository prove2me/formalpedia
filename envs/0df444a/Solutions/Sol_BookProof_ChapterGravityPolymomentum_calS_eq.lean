-- Prove2me | solution 1 for BookProof.ChapterGravityPolymomentum.calS_eq
-- status  : ACCEPTED   (prove)
-- author  : @leonardopedro
-- created : 2026-10-09T14:26:04.092051+00:00
-- url     : https://prove2.me/submissions/50bf2204-f4e7-4b22-b73d-c8e0f0115139

-- Generated from ChapterGravityPolymomentum.lean — solution of BookProof.ChapterGravityPolymomentum.calS_eq
import Mathlib
import Definitions.Def_ChapterGravityPolymomentum
import Theorems.Thm_BookProof_ChapterGravityPolymomentum_metric_transpose
import Theorems.Thm_BookProof_ChapterGravityPolymomentum_proj_add
import Theorems.Thm_BookProof_ChapterGravityPolymomentum_proj_transpose
import Theorems.Thm_BookProof_ChapterGravityPolymomentum_proj_metric
import Theorems.Thm_BookProof_ChapterGravityPolymomentum_vecMulVec_self_transpose
import Theorems.Thm_BookProof_ChapterGravityPolymomentum_proj_polyMom
import Theorems.Thm_BookProof_ChapterGravityPolymomentum_calP_eq
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
    (hSsymm : Sᵀ = S) (hStraceless : (metric * S).trace = 0) (hTcanti : Tcᵀ = -Tc) :
    calS v (polyMom e T S Tc u v) = (2 * e) • S := by

  have hp := proj_polyMom (e := e) (T := T) (u := u) hv hS hTc
  have hAt : (proj v (polyMom e T S Tc u v))ᵀ
      = e • (S - ((4 / 3) * T) • (metric + vecMulVec v v) + Tc) := by
    rw [hp]
    simp only [Matrix.transpose_smul, Matrix.transpose_sub, Matrix.transpose_add, hSsymm,
      metric_transpose, vecMulVec_self_transpose, hTcanti]
    module
  have hP := calP_eq (e := e) (T := T) (u := u) hv hS hTc hStraceless hTcanti
  rw [calS, proj_add, proj_transpose, hAt, hp, hP, proj_metric v hv]
  module
