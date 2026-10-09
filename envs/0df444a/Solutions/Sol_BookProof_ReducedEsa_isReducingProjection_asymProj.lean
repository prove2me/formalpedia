-- Prove2me | solution 1 for BookProof.ReducedEsa.isReducingProjection_asymProj
-- status  : ACCEPTED   (prove)
-- author  : @leonardopedro
-- created : 2026-10-09T08:47:16.833903+00:00
-- url     : https://prove2.me/submissions/f739bc4e-1b89-4033-9256-a6da1824b3b0

-- Generated from ChapterReducingSubspaceEsa.lean — solution of BookProof.ReducedEsa.isReducingProjection_asymProj
import Mathlib
import Definitions.Def_ChapterReducingSubspaceEsa
import Theorems.Thm_BookProof_ReducedEsa_symmetric_of_involutive_isometry
open BookProof.ReducedEsa




open BookProof.FarisLavine BookProof.GraphCore

noncomputable section

variable {F : Type*} [NormedAddCommGroup F] [InnerProductSpace ℂ F]

variable {F : Type*} [NormedAddCommGroup F] [InnerProductSpace ℂ F]
variable {P : F →ₗ[ℂ] F}
variable {D : Submodule ℂ F}
variable (T : D →ₗ[ℂ] F)
variable {T}
variable (U : F →ₗ[ℂ] F)
variable {U}

set_option maxHeartbeats 1000000 in
theorem solution (hU2 : ∀ x, U (U x) = x)
    (hUi : ∀ x y : F, (inner ℂ (U x) (U y) : ℂ) = inner ℂ x y) :
    IsReducingProjection (asymProj U) where
    idem x := by
      simp only [asymProj_apply, map_smul, map_sub, hU2]
      rw [smul_sub, smul_smul]
      module
    symm x y := by
      simp only [asymProj_apply, inner_smul_left, inner_smul_right, inner_sub_left,
        inner_sub_right, symmetric_of_involutive_isometry hU2 hUi x y, map_inv₀, map_ofNat]
