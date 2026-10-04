-- Prove2me | solution 1 for BookProof.NavierStokesFlow.nsHamiltonian_hasZeroDeficiency
-- status  : ACCEPTED   (prove)
-- author  : @leonardopedro
-- created : 2026-10-03T03:44:19.903518+00:00
-- url     : https://prove2.me/submissions/973ba668-d321-44b1-a517-53e149126674

-- Generated from ChapterNavierStokesFlow.lean — solution of BookProof.NavierStokesFlow.nsHamiltonian_hasZeroDeficiency
import Mathlib
import Definitions.Def_ChapterNavierStokesFlow
import Theorems.Thm_BookProof_NavierStokesFlow_nsHamiltonian_hermitian
import Theorems.Thm_BookProof_NavierStokesFlow_symmetric_hasZeroDeficiency
open BookProof.NavierStokesFlow



open scoped BigOperators Matrix Kronecker ComplexOrder TensorProduct

variable {E : Type*} [AddCommGroup E] [Module ℂ E] {ι : Type*} [Fintype ι]
variable {n : ℕ} (L : LagrangianNS n)
variable {n : ℕ} (d : NSTruncation n)
variable {F : Type*} [NormedAddCommGroup F] [InnerProductSpace ℂ F]

set_option maxHeartbeats 1000000 in
theorem solution :
    HasZeroDeficiency (Matrix.toEuclideanLin (nsHamiltonian d)) :=
  symmetric_hasZeroDeficiency _
      (Matrix.isHermitian_iff_isSymmetric.mp (nsHamiltonian_hermitian d))
