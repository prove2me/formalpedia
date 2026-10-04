-- Prove2me | solution 1 for BookProof.NavierStokesFlow.farisLavine_holds_of_everywhereDefined
-- status  : ACCEPTED   (prove)
-- author  : @leonardopedro
-- created : 2026-10-03T03:28:01.441091+00:00
-- url     : https://prove2.me/submissions/51ba73d1-1055-48a5-ad80-c11cd3691331

-- Generated from ChapterNavierStokesFlow.lean — solution of BookProof.NavierStokesFlow.farisLavine_holds_of_everywhereDefined
import Mathlib
import Definitions.Def_ChapterNavierStokesFlow
import Theorems.Thm_BookProof_NavierStokesFlow_symmetric_hasZeroDeficiency
open BookProof.NavierStokesFlow



open scoped BigOperators Matrix Kronecker ComplexOrder TensorProduct

variable {E : Type*} [AddCommGroup E] [Module ℂ E] {ι : Type*} [Fintype ι]
variable {n : ℕ} (L : LagrangianNS n)
variable {n : ℕ} (d : NSTruncation n)
variable {F : Type*} [NormedAddCommGroup F] [InnerProductSpace ℂ F]

set_option maxHeartbeats 1000000 in
theorem solution :
    ∀ (H' N' : F →ₗ[ℂ] F) (a b : ℝ), H'.IsSymmetric →
      (∀ v : F, ‖H' v‖ ≤ a * ‖N' v‖) →
      (∀ v : F, ‖(inner ℂ v (H' (N' v) - N' (H' v)) : ℂ)‖ ≤ b * ‖(inner ℂ v (N' v) : ℂ)‖) →
      HasZeroDeficiency H' := fun H' _ _ _ hsym _ _ => symmetric_hasZeroDeficiency H' hsym
