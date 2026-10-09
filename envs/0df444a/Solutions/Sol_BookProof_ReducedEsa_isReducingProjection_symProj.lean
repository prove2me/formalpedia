-- Prove2me | solution 1 for BookProof.ReducedEsa.isReducingProjection_symProj
-- status  : ACCEPTED   (prove)
-- author  : @leonardopedro
-- created : 2026-10-09T08:46:51.303079+00:00
-- url     : https://prove2.me/submissions/fd6c60e6-d18c-453f-8f0a-ca15981e8710

-- Generated from ChapterReducingSubspaceEsa.lean — solution of BookProof.ReducedEsa.isReducingProjection_symProj
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
    IsReducingProjection (symProj U) where
    idem x := by
      simp only [symProj_apply, map_smul, map_add, hU2]
      rw [smul_add, smul_smul]
      module
    symm x y := by
      simp only [symProj_apply, inner_smul_left, inner_smul_right, inner_add_left,
        inner_add_right, symmetric_of_involutive_isometry hU2 hUi x y, map_inv₀, map_ofNat]
