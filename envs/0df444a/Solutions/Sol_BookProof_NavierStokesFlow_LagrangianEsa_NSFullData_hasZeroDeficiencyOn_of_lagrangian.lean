-- Prove2me | solution 1 for BookProof.NavierStokesFlow.LagrangianEsa.NSFullData.hasZeroDeficiencyOn_of_lagrangian
-- status  : ACCEPTED   (prove)
-- author  : @leonardopedro
-- created : 2026-10-07T12:38:06.617915+00:00
-- url     : https://prove2.me/submissions/558a66d2-cca7-494e-8923-2e327ce11256

-- Generated from ChapterNavierStokesLagrangianEsa.lean — solution of BookProof.NavierStokesFlow.LagrangianEsa.NSFullData.hasZeroDeficiencyOn_of_lagrangian
import Mathlib
import Definitions.Def_ChapterNavierStokesLagrangianEsa
import Theorems.Thm_BookProof_NavierStokesFlow_LagrangianEsa_hasZeroDeficiencyOn_of_linearIsometryEquiv
open BookProof.NavierStokesFlow
open BookProof.NavierStokesFlow.LagrangianEsa





open FullEsa

variable {F : Type*} [NormedAddCommGroup F] [InnerProductSpace ℂ F]
variable (L : LagrangianFullData F)
variable {F G : Type*} [NormedAddCommGroup F] [InnerProductSpace ℂ F]
  [NormedAddCommGroup G] [InnerProductSpace ℂ G]

set_option maxHeartbeats 1000000 in
theorem solution (d : FullEsa.NSFullData F)
    (L : LagrangianFullData G) (W : F ≃ₗᵢ[ℂ] G) (hmap : ∀ x : d.D, W (x : F) ∈ L.D)
    (hsurj : ∀ y : L.D, ∃ x : d.D, W (x : F) = (y : G))
    (hint : ∀ x : d.D, (L.hFull ⟨W (x : F), hmap x⟩ : G) = W ((d.hamiltonian x : F)))
    (hL : HasZeroDeficiencyOn L.D L.hFull) :
    HasZeroDeficiencyOn d.D d.hamiltonian := hasZeroDeficiencyOn_of_linearIsometryEquiv W hmap hsurj hint hL
