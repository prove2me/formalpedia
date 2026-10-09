-- Prove2me | solution 1 for BookProof.GraphCore.isGraphCore_pushOp
-- status  : ACCEPTED   (prove)
-- author  : @leonardopedro
-- created : 2026-10-09T07:50:46.004598+00:00
-- url     : https://prove2.me/submissions/748a51db-0e02-4581-b705-2981a6d90b21

-- Generated from ChapterGraphCoreTransfer.lean — solution of BookProof.GraphCore.isGraphCore_pushOp
import Mathlib
import Definitions.Def_ChapterGraphCoreTransfer
import Theorems.Thm_BookProof_GraphCore_mem_pushDom
import Theorems.Thm_BookProof_GraphCore_pushOp_apply
open BookProof.GraphCore




open BookProof.FarisLavine

variable {F : Type*} [NormedAddCommGroup F] [InnerProductSpace ℂ F]

variable {F : Type*} [NormedAddCommGroup F] [InnerProductSpace ℂ F]
variable {G : Type*} [NormedAddCommGroup G] [InnerProductSpace ℂ G]

set_option maxHeartbeats 1000000 in
theorem solution (U : F →ₗᵢ[ℂ] G) {D₁ D₂ : Submodule ℂ F} (T : D₂ →ₗ[ℂ] F)
    (hcore : IsGraphCore D₁ T) : IsGraphCore (pushDom U D₁) (pushOp U T) := by

  intro x ε hε
  obtain ⟨x₀, hx₀, hxe⟩ := x.2
  have hx' : (x : G) = U ((⟨x₀, hx₀⟩ : D₂) : F) := hxe.symm
  obtain ⟨y₀, hy₀D₁, hy₁, hy₂⟩ := hcore ⟨x₀, hx₀⟩ ε hε
  refine ⟨⟨U (y₀ : F), mem_pushDom U y₀⟩, ⟨(y₀ : F), hy₀D₁, rfl⟩, ?_, ?_⟩
  · have hh : (x : G) - U (y₀ : F) = U ((⟨x₀, hx₀⟩ : D₂) - y₀ : F) := by
      rw [map_sub, ← hx']
    rw [hh, U.norm_map]
    exact hy₁
  · rw [pushOp_apply U T x ⟨x₀, hx₀⟩ hx',
      pushOp_apply U T ⟨U (y₀ : F), mem_pushDom U y₀⟩ y₀ rfl, ← map_sub, U.norm_map]
    exact hy₂
