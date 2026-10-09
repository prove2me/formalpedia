-- Prove2me | solution 1 for BookProof.GraphCore.symmetricOn_pushOp
-- status  : ACCEPTED   (prove)
-- author  : @leonardopedro
-- created : 2026-10-09T07:50:09.234274+00:00
-- url     : https://prove2.me/submissions/ed1235a6-e54a-4ceb-adba-e93d273ecdb0

-- Generated from ChapterGraphCoreTransfer.lean — solution of BookProof.GraphCore.symmetricOn_pushOp
import Mathlib
import Definitions.Def_ChapterGraphCoreTransfer
import Theorems.Thm_BookProof_GraphCore_pushOp_apply
open BookProof.GraphCore




open BookProof.FarisLavine

variable {F : Type*} [NormedAddCommGroup F] [InnerProductSpace ℂ F]

variable {F : Type*} [NormedAddCommGroup F] [InnerProductSpace ℂ F]
variable {G : Type*} [NormedAddCommGroup G] [InnerProductSpace ℂ G]

set_option maxHeartbeats 1000000 in
theorem solution (U : F →ₗᵢ[ℂ] G) {D : Submodule ℂ F} (T : D →ₗ[ℂ] F)
    (hT : SymmetricOn D T) : SymmetricOn (pushDom U D) (pushOp U T) := by

  intro x y
  obtain ⟨x₀, hx₀, hxe⟩ := x.2
  obtain ⟨y₀, hy₀, hye⟩ := y.2
  have hx' : (x : G) = U ((⟨x₀, hx₀⟩ : D) : F) := hxe.symm
  have hy' : (y : G) = U ((⟨y₀, hy₀⟩ : D) : F) := hye.symm
  rw [pushOp_apply U T x ⟨x₀, hx₀⟩ hx', pushOp_apply U T y ⟨y₀, hy₀⟩ hy', hx', hy',
    U.inner_map_map, U.inner_map_map]
  exact hT ⟨x₀, hx₀⟩ ⟨y₀, hy₀⟩
