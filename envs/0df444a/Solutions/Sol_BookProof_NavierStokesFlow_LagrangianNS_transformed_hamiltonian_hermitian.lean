-- Prove2me | solution 1 for BookProof.NavierStokesFlow.LagrangianNS.transformed_hamiltonian_hermitian
-- status  : ACCEPTED   (prove)
-- author  : @leonardopedro
-- created : 2026-10-03T03:44:06.223621+00:00
-- url     : https://prove2.me/submissions/37155a46-5b9d-4d91-bb50-6ef60461fe6a

-- Generated from ChapterNavierStokesFlow.lean — solution of BookProof.NavierStokesFlow.LagrangianNS.transformed_hamiltonian_hermitian
import Mathlib
import Definitions.Def_ChapterNavierStokesFlow
import Theorems.Thm_BookProof_NavierStokesFlow_LagrangianNS_kinetic_posSemidef
import Theorems.Thm_BookProof_NavierStokesFlow_LagrangianNS_viscous_posSemidef
open BookProof.NavierStokesFlow
open BookProof.NavierStokesFlow.LagrangianNS



open scoped BigOperators Matrix Kronecker ComplexOrder TensorProduct

variable {E : Type*} [AddCommGroup E] [Module ℂ E] {ι : Type*} [Fintype ι]
variable {n : ℕ} (L : LagrangianNS n)

set_option maxHeartbeats 1000000 in
theorem solution : (L.hFull)ᴴ = L.hFull := by

  have hk : (L.kinetic)ᴴ = L.kinetic := (kinetic_posSemidef L).isHermitian
  have hv : (L.viscous)ᴴ = L.viscous := (viscous_posSemidef L).isHermitian
  have hd : (L.drift)ᴴ = L.drift := by
    simp only [drift, Matrix.conjTranspose_sum, Matrix.conjTranspose_smul, L.D_herm,
      star_trivial]
  simp only [hFull, Matrix.conjTranspose_add, hk, hv, hd, L.C_herm]
