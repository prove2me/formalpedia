-- Prove2me | solution 1 for BookProof.GraphCore.pushOp_apply
-- status  : ACCEPTED   (prove)
-- author  : @leonardopedro
-- created : 2026-10-09T07:50:08.071864+00:00
-- url     : https://prove2.me/submissions/73173685-21a7-417d-9bd3-5d320fd111c7

-- Generated from ChapterGraphCoreTransfer.lean — solution of BookProof.GraphCore.pushOp_apply
import Mathlib
import Definitions.Def_ChapterGraphCoreTransfer
open BookProof.GraphCore




open BookProof.FarisLavine

variable {F : Type*} [NormedAddCommGroup F] [InnerProductSpace ℂ F]

variable {F : Type*} [NormedAddCommGroup F] [InnerProductSpace ℂ F]
variable {G : Type*} [NormedAddCommGroup G] [InnerProductSpace ℂ G]

set_option maxHeartbeats 1000000 in
theorem solution (U : F →ₗᵢ[ℂ] G) {D : Submodule ℂ F} (T : D →ₗ[ℂ] F)
    (x : pushDom U D) (x₀ : D) (hx : (x : G) = U (x₀ : F)) :
    pushOp U T x = U (T x₀) := by

  have hxx : (Submodule.equivMapOfInjective U.toLinearMap U.injective D) x₀ = x := by
    apply Subtype.ext; rw [hx]; rfl
  have h2 : (Submodule.equivMapOfInjective U.toLinearMap U.injective D).symm x = x₀ := by
    rw [← hxx]; simp
  exact congrArg (fun z : D => U (T z)) h2
