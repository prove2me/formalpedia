-- Prove2me | solution 1 for BookProof.NavierStokesFlow.nsFlow_groupOnEvolved
-- status  : ACCEPTED   (prove)
-- author  : @leonardopedro
-- created : 2026-10-03T03:27:06.671252+00:00
-- url     : https://prove2.me/submissions/28800b81-5698-4508-8a78-cffe553f0180

-- Generated from ChapterNavierStokesFlow.lean — solution of BookProof.NavierStokesFlow.nsFlow_groupOnEvolved
import Mathlib
import Definitions.Def_ChapterNavierStokesFlow
import Theorems.Thm_BookProof_NavierStokesFlow_nsFlow_group
open BookProof.NavierStokesFlow



open scoped BigOperators Matrix Kronecker ComplexOrder TensorProduct

variable {E : Type*} [AddCommGroup E] [Module ℂ E] {ι : Type*} [Fintype ι]
variable {n : ℕ} (L : LagrangianNS n)
variable {n : ℕ} (d : NSTruncation n)

set_option maxHeartbeats 1000000 in
theorem solution (t₁ t₂ : ℝ) (psi : Fin n → ℂ) :
    nsFlowUnitary d t₁ *ᵥ (nsFlowUnitary d t₂ *ᵥ psi) = nsFlowUnitary d (t₁ + t₂) *ᵥ psi := by

  rw [nsFlow_group, Matrix.mulVec_mulVec]
