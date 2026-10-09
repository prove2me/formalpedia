-- Prove2me | solution 1 for BookProof.ReducedEsa.symmetricOn_redOp
-- status  : ACCEPTED   (prove)
-- author  : @leonardopedro
-- created : 2026-10-09T08:46:12.337189+00:00
-- url     : https://prove2.me/submissions/f8fb8118-e197-4384-8d24-07f6c3850454

-- Generated from ChapterReducingSubspaceEsa.lean — solution of BookProof.ReducedEsa.symmetricOn_redOp
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
variable (T) in

set_option maxHeartbeats 1000000 in
theorem solution (hP : IsReducingProjection P) {hPD : ∀ x ∈ D, P x ∈ D}
    (hC : Commutes T hPD) (hT : SymmetricOn D T) :
    SymmetricOn (redDom P D) (redOp T hP hC) := by

  intro x y
  have hx := hT (redIncl P D x) (redIncl P D y)
  simpa [Submodule.coe_inner] using hx
