-- Prove2me | solution 1 for BookProof.NavierStokesFlow.nsHamiltonian_hasZeroDeficiencyOn
-- status  : ACCEPTED   (prove)
-- author  : @leonardopedro
-- created : 2026-10-03T03:45:13.842604+00:00
-- url     : https://prove2.me/submissions/69690234-00a5-4a74-8f85-ee51cb9b8015

-- Generated from ChapterNavierStokesFlow.lean — solution of BookProof.NavierStokesFlow.nsHamiltonian_hasZeroDeficiencyOn
import Mathlib
import Definitions.Def_ChapterNavierStokesFlow
import Theorems.Thm_BookProof_NavierStokesFlow_nsHamiltonian_hermitian
import Theorems.Thm_BookProof_NavierStokesFlow_hasZeroDeficiencyOn_top_of_symmetric
open BookProof.NavierStokesFlow



open scoped BigOperators Matrix Kronecker ComplexOrder TensorProduct

variable {E : Type*} [AddCommGroup E] [Module ℂ E] {ι : Type*} [Fintype ι]
variable {n : ℕ} (L : LagrangianNS n)
variable {n : ℕ} (d : NSTruncation n)
variable {F : Type*} [NormedAddCommGroup F] [InnerProductSpace ℂ F]

set_option maxHeartbeats 1000000 in
theorem solution :
    HasZeroDeficiencyOn (⊤ : Submodule ℂ (EuclideanSpace ℂ (Fin n)))
      (restrictToTop (Matrix.toEuclideanLin (nsHamiltonian d))) :=
  hasZeroDeficiencyOn_top_of_symmetric _
      (Matrix.isHermitian_iff_isSymmetric.mp (nsHamiltonian_hermitian d))
