-- Prove2me | solution 1 for BookProof.NavierStokesFlow.FullEsa.latticeFullHamiltonianCLM_isSymmetric
-- status  : ACCEPTED   (prove)
-- author  : @leonardopedro
-- created : 2026-10-11T08:19:40.455958+00:00
-- url     : https://prove2.me/submissions/ce738954-9620-48fd-b16f-a8cefd9dd829

-- Generated from ChapterNavierStokesFullEsa.lean — solution of BookProof.NavierStokesFlow.FullEsa.latticeFullHamiltonianCLM_isSymmetric
import Mathlib
import Definitions.Def_ChapterNavierStokesFullEsa
import Theorems.Thm_BookProof_NavierStokesFlow_FullEsa_latticeFullHamiltonianCLM_isSelfAdjoint
import Definitions.Def_ChapterContinuityUnitaryInfinite
import Definitions.Def_ChapterNavierStokesAffineFiberEsa
open BookProof.NavierStokesFlow
open BookProof.NavierStokesFlow.FullEsa



open scoped ENNReal
open BookProof.ChapterContinuityUnitaryInfinite

variable {F : Type*} [NormedAddCommGroup F] [InnerProductSpace ℂ F]
variable {D : Submodule ℂ F}
variable (d : NSFullData F)

set_option maxHeartbeats 1000000 in

theorem solution (v : Fin 15 → LinfZ) (nu : ℝ) :
    ((latticeFullHamiltonianCLM v nu : L2Z →L[ℂ] L2Z) : L2Z →ₗ[ℂ] L2Z).IsSymmetric :=
  ContinuousLinearMap.isSelfAdjoint_iff_isSymmetric.1 (latticeFullHamiltonianCLM_isSelfAdjoint v nu)
