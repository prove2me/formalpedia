-- Prove2me | solution 1 for BookProof.NavierStokesFlow.FullEsa.latticeFullHamiltonianCLM_isSelfAdjoint
-- status  : ACCEPTED   (prove)
-- author  : @leonardopedro
-- created : 2026-10-11T08:35:59.842988+00:00
-- url     : https://prove2.me/submissions/b7b93f27-4cb9-4973-8d62-01d98538dc93

-- Generated from ChapterNavierStokesFullEsa.lean — solution of BookProof.NavierStokesFlow.FullEsa.latticeFullHamiltonianCLM_isSelfAdjoint
import Mathlib
import Definitions.Def_ChapterNavierStokesFullEsa
import Theorems.Thm_BookProof_NavierStokesFlow_FullEsa_latticeAdvectionCLM_isSelfAdjoint
import Theorems.Thm_BookProof_ChapterContinuityUnitaryInfinite_momentum_isSelfAdjoint
import Definitions.Def_ChapterContinuityUnitary
import Definitions.Def_ChapterContinuityUnitaryInfinite
import Definitions.Def_ChapterNavierStokesAffineFiberEsa
open BookProof.NavierStokesFlow
open BookProof.NavierStokesFlow.FullEsa



open scoped ENNReal
open BookProof.ChapterContinuityUnitary
open BookProof.ChapterContinuityUnitaryInfinite

variable {F : Type*} [NormedAddCommGroup F] [InnerProductSpace ℂ F]
variable {D : Submodule ℂ F}
variable (d : NSFullData F)

set_option maxHeartbeats 1000000 in

theorem solution (v : Fin 15 → LinfZ) (nu : ℝ) :
    IsSelfAdjoint (latticeFullHamiltonianCLM v nu) := by
  change star (latticeFullHamiltonianCLM v nu) = latticeFullHamiltonianCLM v nu
  rw [latticeFullHamiltonianCLM, star_sum]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [star_add, star_mul, star_mul, (latticeAdvectionCLM_isSelfAdjoint v nu i).star_eq,
    momentum_isSelfAdjoint.star_eq]
  exact add_comm _ _
