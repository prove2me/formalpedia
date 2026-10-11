-- Prove2me | solution 1 for BookProof.NavierStokesFlow.LagrangianEsa.latticeLagCLM_isSymmetric
-- status  : SKETCH_ACCEPTED   (prove)
-- author  : @leonardopedro
-- created : 2026-10-11T08:36:04.258353+00:00
-- url     : https://prove2.me/submissions/80f4e159-ae9d-4a64-9e38-89ea5a67b39e
-- note    : a sketch -- it imports a theorem that is still Open,
--           so it depends on `sorryAx` until that child is proved.

-- Generated from ChapterNavierStokesLagrangianEsa.lean — solution of BookProof.NavierStokesFlow.LagrangianEsa.latticeLagCLM_isSymmetric
import Mathlib
import Definitions.Def_ChapterNavierStokesLagrangianEsa
import Theorems.Thm_BookProof_NavierStokesFlow_LagrangianEsa_latticeLagCLM_isSelfAdjoint
import Definitions.Def_ChapterContinuityUnitaryInfinite
import Definitions.Def_ChapterNavierStokesAffineFiberEsa
open BookProof.NavierStokesFlow
open BookProof.NavierStokesFlow.LagrangianEsa





open FullEsa
open BookProof.ChapterContinuityUnitaryInfinite

variable {F : Type*} [NormedAddCommGroup F] [InnerProductSpace ℂ F]
variable (L : LagrangianFullData F)
variable {F G : Type*} [NormedAddCommGroup F] [InnerProductSpace ℂ F]
  [NormedAddCommGroup G] [InnerProductSpace ℂ G]

set_option maxHeartbeats 1000000 in

theorem solution (v : Fin 3 → LinfZ) (w : LinfZ) (fr : Fin 3 → ℝ) (nu : ℝ) :
    ((latticeLagCLM v w fr nu : L2Z →L[ℂ] L2Z) : L2Z →ₗ[ℂ] L2Z).IsSymmetric :=
  ContinuousLinearMap.isSelfAdjoint_iff_isSymmetric.1 (latticeLagCLM_isSelfAdjoint v w fr nu)
