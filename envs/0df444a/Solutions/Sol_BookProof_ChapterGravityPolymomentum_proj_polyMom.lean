-- Prove2me | solution 1 for BookProof.ChapterGravityPolymomentum.proj_polyMom
-- status  : ACCEPTED   (prove)
-- author  : @leonardopedro
-- created : 2026-10-09T14:25:28.004155+00:00
-- url     : https://prove2.me/submissions/0d73a109-ddf3-48ab-a47c-d49c27d8bb84

-- Generated from ChapterGravityPolymomentum.lean — solution of BookProof.ChapterGravityPolymomentum.proj_polyMom
import Mathlib
import Definitions.Def_ChapterGravityPolymomentum
import Theorems.Thm_BookProof_ChapterGravityPolymomentum_proj_add
import Theorems.Thm_BookProof_ChapterGravityPolymomentum_proj_sub
import Theorems.Thm_BookProof_ChapterGravityPolymomentum_proj_smul
import Theorems.Thm_BookProof_ChapterGravityPolymomentum_proj_eq_self_of_spatial
import Theorems.Thm_BookProof_ChapterGravityPolymomentum_proj_vecMulVec_right
import Theorems.Thm_BookProof_ChapterGravityPolymomentum_proj_metric
import Definitions.Def_ChapterElectroweakFieldStrength
import Definitions.Def_ChapterGravityProjector
open BookProof.ChapterGravityPolymomentum




open Matrix
open scoped BigOperators
open BookProof.ChapterGravityProjector
open BookProof.ChapterElectroweakFieldStrength

variable {e T : ℝ} {S Tc : Matrix (Fin 4) (Fin 4) ℝ} {u v : Fin 4 → ℝ}

set_option maxHeartbeats 1000000 in
theorem solution (hv : minkSq v = -1) (hS : IsSpatial v S) (hTc : IsSpatial v Tc) :
    proj v (polyMom e T S Tc u v)
      = e • (S - ((4 / 3) * T) • (metric + vecMulVec v v) - Tc) := by

  rw [polyMom, proj_smul, proj_add, proj_sub, proj_sub, proj_smul, proj_smul,
    proj_eq_self_of_spatial v hS, proj_eq_self_of_spatial v hTc,
    proj_metric v hv, proj_vecMulVec_right v hv u]
  simp
