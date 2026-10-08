-- Prove2me | solution 1 for BookProof.NavierStokesFlow.LagrangianEsa.LagrangianFullData.isSymmetricDom_sq
-- status  : ACCEPTED   (prove)
-- author  : @leonardopedro
-- created : 2026-10-07T12:16:04.092682+00:00
-- url     : https://prove2.me/submissions/1bcf7e80-76f1-4966-aaae-655f40f4d7ef

-- Generated from ChapterNavierStokesLagrangianEsa.lean — solution of BookProof.NavierStokesFlow.LagrangianEsa.LagrangianFullData.isSymmetricDom_sq
import Mathlib
import Definitions.Def_ChapterNavierStokesLagrangianEsa
import Theorems.Thm_BookProof_NavierStokesFlow_FullEsa_IsSymmetricDom_comp_of_commute
open BookProof.NavierStokesFlow
open BookProof.NavierStokesFlow.LagrangianEsa
open BookProof.NavierStokesFlow.LagrangianEsa.LagrangianFullData





open FullEsa

variable {F : Type*} [NormedAddCommGroup F] [InnerProductSpace ℂ F]
variable (L : LagrangianFullData F)

set_option maxHeartbeats 1000000 in
theorem solution {D : Submodule ℂ F} {A : D →ₗ[ℂ] D} (hA : IsSymmetricDom A) :
    IsSymmetricDom (A.comp A) := hA.comp_of_commute hA rfl
