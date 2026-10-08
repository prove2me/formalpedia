-- Prove2me | solution 1 for BookProof.NavierStokesFlow.LagrangianEsa.LagrangianFullData.hasZeroDeficiencyOn_of_boundedRealization
-- status  : ACCEPTED   (prove)
-- author  : @leonardopedro
-- created : 2026-10-07T12:30:02.012704+00:00
-- url     : https://prove2.me/submissions/ed521526-8d60-446d-8fc8-08ea3e72c47a

-- Generated from ChapterNavierStokesLagrangianEsa.lean — solution of BookProof.NavierStokesFlow.LagrangianEsa.LagrangianFullData.hasZeroDeficiencyOn_of_boundedRealization
import Mathlib
import Definitions.Def_ChapterNavierStokesLagrangianEsa
import Theorems.Thm_BookProof_NavierStokesFlow_FullEsa_hasZeroDeficiencyOn_of_boundedRealization
open BookProof.NavierStokesFlow
open BookProof.NavierStokesFlow.LagrangianEsa
open BookProof.NavierStokesFlow.LagrangianEsa.LagrangianFullData





open FullEsa

variable {F : Type*} [NormedAddCommGroup F] [InnerProductSpace ℂ F]
variable (L : LagrangianFullData F)

set_option maxHeartbeats 1000000 in
theorem solution (A : F →L[ℂ] F)
    (hsym : (A : F →ₗ[ℂ] F).IsSymmetric) (hHA : ∀ x : L.D, (L.hFull x : F) = A (x : F)) :
    HasZeroDeficiencyOn L.D L.hFull := FullEsa.hasZeroDeficiencyOn_of_boundedRealization L.hFull A hsym L.dense hHA
