-- Prove2me | solution 1 for BookProof.NavierStokesFlow.nsFlow_noBlowup
-- status  : ACCEPTED   (prove)
-- author  : @leonardopedro
-- created : 2026-10-03T03:58:18.434063+00:00
-- url     : https://prove2.me/submissions/01d12ebd-f29e-45fd-b0fe-286ca117d17c

-- Generated from ChapterNavierStokesFlow.lean — solution of BookProof.NavierStokesFlow.nsFlow_noBlowup
import Mathlib
import Definitions.Def_ChapterNavierStokesFlow
import Theorems.Thm_BookProof_NavierStokesFlow_nsFlow_norm_preserving
open BookProof.NavierStokesFlow



open scoped BigOperators Matrix Kronecker ComplexOrder TensorProduct

variable {E : Type*} [AddCommGroup E] [Module ℂ E] {ι : Type*} [Fintype ι]
variable {n : ℕ} (L : LagrangianNS n)
variable {n : ℕ} (d : NSTruncation n)

set_option maxHeartbeats 1000000 in
theorem solution (t : ℝ) (psi : Fin n → ℂ) (k : Fin n) :
    ‖(nsFlowUnitary d t *ᵥ psi) k‖ ^ 2 ≤ ∑ a, ‖psi a‖ ^ 2 := by

  rw [← nsFlow_norm_preserving d t psi]
  exact Finset.single_le_sum (f := fun a => ‖(nsFlowUnitary d t *ᵥ psi) a‖ ^ 2)
    (fun a _ => by positivity) (Finset.mem_univ k)
