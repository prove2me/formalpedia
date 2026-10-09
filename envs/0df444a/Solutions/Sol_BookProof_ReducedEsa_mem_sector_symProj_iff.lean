-- Prove2me | solution 1 for BookProof.ReducedEsa.mem_sector_symProj_iff
-- status  : ACCEPTED   (prove)
-- author  : @leonardopedro
-- created : 2026-10-09T08:47:29.960272+00:00
-- url     : https://prove2.me/submissions/ecce4425-7729-4a22-8aba-490d66d0c72c

-- Generated from ChapterReducingSubspaceEsa.lean — solution of BookProof.ReducedEsa.mem_sector_symProj_iff
import Mathlib
import Definitions.Def_ChapterReducingSubspaceEsa
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
theorem solution (hU2 : ∀ x, U (U x) = x) {x : F} :
    x ∈ sector (symProj U) ↔ U x = x := by

  constructor
  · rintro ⟨u, rfl⟩
    simp only [symProj_apply, map_smul, map_add, hU2]
    rw [smul_add, smul_add]
    abel
  · intro hx
    exact ⟨x, by simp [symProj, hx]; module⟩
