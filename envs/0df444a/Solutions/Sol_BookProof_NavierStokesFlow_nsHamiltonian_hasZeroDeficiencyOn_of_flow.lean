-- Prove2me | solution 1 for BookProof.NavierStokesFlow.nsHamiltonian_hasZeroDeficiencyOn_of_flow
-- status  : ACCEPTED   (prove)
-- author  : @leonardopedro
-- created : 2026-09-13T13:20:48.433483+00:00
-- url     : https://prove2.me/submissions/5dc9a032-3ec7-45b6-b0ee-7b7daab2c6bd

-- Generated from ChapterNavierStokesEsa.lean — solution of BookProof.NavierStokesFlow.nsHamiltonian_hasZeroDeficiencyOn_of_flow
import Mathlib
import Definitions.Def_ChapterNavierStokesEsa
import Theorems.Thm_BookProof_NavierStokesFlow_hasZeroDeficiencyOn_of_completeUnitaryFlow
import Theorems.Thm_BookProof_NavierStokesFlow_nsFlowEuclidean_norm
import Theorems.Thm_BookProof_NavierStokesFlow_nsFlowEuclidean_zero
import Theorems.Thm_BookProof_NavierStokesFlow_nsFlowEuclidean_hasDerivAt
import Definitions.Def_ChapterContinuityUnitaryInfinite
open BookProof.NavierStokesFlow









open scoped Matrix



variable {F : Type*} [NormedAddCommGroup F] [InnerProductSpace ℂ F]

















variable {ι : Type*}









open BookProof.ChapterContinuityUnitaryInfinite














variable {n : ℕ} (d : NSTruncation n)

set_option maxHeartbeats 1000000 in
theorem solution :
    HasZeroDeficiencyOn (⊤ : Submodule ℂ (EuclideanSpace ℂ (Fin n)))
      (restrictToTop (Matrix.toEuclideanLin (nsHamiltonian d))) :=
  hasZeroDeficiencyOn_of_completeUnitaryFlow _ _ (nsFlowEuclidean d)
      (by simp) (fun t psi => nsFlowEuclidean_norm d t psi)
      (fun psi => nsFlowEuclidean_zero d psi) (fun _ _ => trivial)
      (fun psi t => nsFlowEuclidean_hasDerivAt d (psi : EuclideanSpace ℂ (Fin n)) t)
