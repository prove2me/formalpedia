-- Prove2me | solution 1 for BookProof.NavierStokesFlow.nsFlow_norm_preserving
-- status  : ACCEPTED   (prove)
-- author  : @leonardopedro
-- created : 2026-10-03T03:45:52.126429+00:00
-- url     : https://prove2.me/submissions/6910f4eb-ae6f-40ed-a609-0c7bdf35296e

-- Generated from ChapterNavierStokesFlow.lean — solution of BookProof.NavierStokesFlow.nsFlow_norm_preserving
import Mathlib
import Definitions.Def_ChapterNavierStokesFlow
import Theorems.Thm_BookProof_NavierStokesFlow_nsFlow_unitary
open BookProof.NavierStokesFlow



open scoped BigOperators Matrix Kronecker ComplexOrder TensorProduct

variable {E : Type*} [AddCommGroup E] [Module ℂ E] {ι : Type*} [Fintype ι]
variable {n : ℕ} (L : LagrangianNS n)
variable {n : ℕ} (d : NSTruncation n)

set_option maxHeartbeats 1000000 in
theorem solution (t : ℝ) (psi : Fin n → ℂ) :
    ∑ a, ‖(nsFlowUnitary d t *ᵥ psi) a‖ ^ 2 = ∑ a, ‖psi a‖ ^ 2 := BookProof.ChapterContinuityUnitary.unitary_preserves_normSq _ (nsFlow_unitary d t) psi
