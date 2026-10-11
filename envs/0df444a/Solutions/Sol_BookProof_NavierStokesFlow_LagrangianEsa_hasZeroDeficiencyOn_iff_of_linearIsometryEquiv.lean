-- Prove2me | solution 1 for BookProof.NavierStokesFlow.LagrangianEsa.hasZeroDeficiencyOn_iff_of_linearIsometryEquiv
-- status  : ACCEPTED   (prove)
-- author  : @leonardopedro
-- created : 2026-10-10T23:39:25.344412+00:00
-- url     : https://prove2.me/submissions/da5b55e2-a2e5-496a-9ee1-050180c456d3

-- Generated from ChapterNavierStokesLagrangianEsa.lean — solution of BookProof.NavierStokesFlow.LagrangianEsa.hasZeroDeficiencyOn_iff_of_linearIsometryEquiv
import Mathlib
import Definitions.Def_ChapterNavierStokesLagrangianEsa
import Theorems.Thm_BookProof_NavierStokesFlow_LagrangianEsa_hasZeroDeficiencyOn_of_linearIsometryEquiv
import Theorems.Thm_BookProof_NavierStokesFlow_LagrangianEsa_hasZeroDeficiencyOn_map_of_linearIsometryEquiv
import Definitions.Def_ChapterNavierStokesFlow
import Definitions.Def_ChapterNavierStokesAffineFiberEsa
open BookProof.NavierStokesFlow
open BookProof.NavierStokesFlow.LagrangianEsa





open FullEsa

variable {F : Type*} [NormedAddCommGroup F] [InnerProductSpace ℂ F]
variable (L : LagrangianFullData F)
variable {F G : Type*} [NormedAddCommGroup F] [InnerProductSpace ℂ F]
  [NormedAddCommGroup G] [InnerProductSpace ℂ G]

set_option maxHeartbeats 1000000 in
theorem solution (W : F ≃ₗᵢ[ℂ] G) {D : Submodule ℂ F}
    {D' : Submodule ℂ G} {H : D →ₗ[ℂ] D} {H' : D' →ₗ[ℂ] D'}
    (hmap : ∀ x : D, W (x : F) ∈ D') (hsurj : ∀ y : D', ∃ x : D, W (x : F) = (y : G))
    (hint : ∀ x : D, (H' ⟨W (x : F), hmap x⟩ : G) = W ((H x : F))) :
    HasZeroDeficiencyOn D H ↔ HasZeroDeficiencyOn D' H' :=
  ⟨hasZeroDeficiencyOn_map_of_linearIsometryEquiv W hmap hint,
      hasZeroDeficiencyOn_of_linearIsometryEquiv W hmap hsurj hint⟩
