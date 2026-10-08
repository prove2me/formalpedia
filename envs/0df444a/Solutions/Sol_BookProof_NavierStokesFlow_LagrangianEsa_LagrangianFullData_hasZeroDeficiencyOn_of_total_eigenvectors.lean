-- Prove2me | solution 1 for BookProof.NavierStokesFlow.LagrangianEsa.LagrangianFullData.hasZeroDeficiencyOn_of_total_eigenvectors
-- status  : ACCEPTED   (prove)
-- author  : @leonardopedro
-- created : 2026-10-07T12:08:43.852302+00:00
-- url     : https://prove2.me/submissions/4ec71fa7-122a-4013-a365-5f768e092598

-- Generated from ChapterNavierStokesLagrangianEsa.lean — solution of BookProof.NavierStokesFlow.LagrangianEsa.LagrangianFullData.hasZeroDeficiencyOn_of_total_eigenvectors
import Mathlib
import Definitions.Def_ChapterNavierStokesLagrangianEsa
import Theorems.Thm_BookProof_NavierStokesFlow_hasZeroDeficiencyOn_of_total_eigenvectors
open BookProof.NavierStokesFlow
open BookProof.NavierStokesFlow.LagrangianEsa
open BookProof.NavierStokesFlow.LagrangianEsa.LagrangianFullData





open FullEsa

variable {F : Type*} [NormedAddCommGroup F] [InnerProductSpace ℂ F]
variable (L : LagrangianFullData F)

set_option maxHeartbeats 1000000 in
theorem solution {I : Type*} (e : I → L.D) (lam : I → ℝ)
    (heig : ∀ a, L.hFull (e a) = ((lam a : ℝ) : ℂ) • e a)
    (htotal : ∀ w : F, (∀ a, (inner ℂ ((e a : F)) w : ℂ) = 0) → w = 0) :
    HasZeroDeficiencyOn L.D L.hFull :=
  _root_.BookProof.NavierStokesFlow.hasZeroDeficiencyOn_of_total_eigenvectors
      L.D L.hFull e lam heig htotal
