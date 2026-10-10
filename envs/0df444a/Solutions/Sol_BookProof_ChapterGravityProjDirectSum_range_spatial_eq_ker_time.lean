-- Prove2me | solution 1 for BookProof.ChapterGravityProjDirectSum.range_spatial_eq_ker_time
-- status  : ACCEPTED   (prove)
-- author  : @leonardopedro
-- created : 2026-10-09T14:29:25.268879+00:00
-- url     : https://prove2.me/submissions/e804e406-b5a7-4ad5-8d61-d2ca17bc255a

-- Generated from ChapterGravityProjDirectSum.lean — solution of BookProof.ChapterGravityProjDirectSum.range_spatial_eq_ker_time
import Mathlib
import Definitions.Def_ChapterGravityProjDirectSum
import Theorems.Thm_BookProof_ChapterGravityProjDirectSum_mulVecLin_spatial_add_time
import Theorems.Thm_BookProof_ChapterGravityProjDirectSum_mulVecLin_time_comp_spatial
import Definitions.Def_ChapterGravityProjector
import Definitions.Def_ChapterGravityTimeProj
open BookProof.ChapterGravityProjDirectSum



open Matrix


open BookProof.ChapterGravityProjector
open BookProof.ChapterGravityTimeProj

set_option maxHeartbeats 1000000 in
theorem solution (v : Fin 4 → ℝ) (hv : minkSq v = -1) :
    LinearMap.range (spatialProj v).mulVecLin
      = LinearMap.ker (timeProj v).mulVecLin := by

  apply le_antisymm
  · rintro x ⟨a, rfl⟩
    have := congrArg (fun L : (Fin 4 → ℝ) →ₗ[ℝ] (Fin 4 → ℝ) => L a)
      (mulVecLin_time_comp_spatial v hv)
    simpa [LinearMap.mem_ker] using this
  · intro x hx
    have hid : (spatialProj v).mulVecLin x + (timeProj v).mulVecLin x = x := by
      have := congrArg (fun L : (Fin 4 → ℝ) →ₗ[ℝ] (Fin 4 → ℝ) => L x)
        (mulVecLin_spatial_add_time v)
      simpa using this
    rw [LinearMap.mem_ker] at hx
    rw [hx, add_zero] at hid
    exact ⟨x, hid⟩
