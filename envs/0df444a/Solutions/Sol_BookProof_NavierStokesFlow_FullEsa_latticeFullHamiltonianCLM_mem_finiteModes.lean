-- Prove2me | solution 1 for BookProof.NavierStokesFlow.FullEsa.latticeFullHamiltonianCLM_mem_finiteModes
-- status  : ACCEPTED   (prove)
-- author  : @leonardopedro
-- created : 2026-10-11T08:19:43.967085+00:00
-- url     : https://prove2.me/submissions/0b1d8115-06b6-4c4f-8d11-8e7d2fdec562

-- Generated from ChapterNavierStokesFullEsa.lean — solution of BookProof.NavierStokesFlow.FullEsa.latticeFullHamiltonianCLM_mem_finiteModes
import Mathlib
import Definitions.Def_ChapterNavierStokesFullEsa
import Theorems.Thm_BookProof_NavierStokesFlow_FullEsa_latticeAdvectionCLM_mem_finiteModes
import Definitions.Def_ChapterContinuityUnitary
import Definitions.Def_ChapterContinuityUnitaryInfinite
import Definitions.Def_ChapterNavierStokesEsa
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

theorem solution (v : Fin 15 → LinfZ) (nu : ℝ)
    {f : L2Z} (hf : f ∈ finiteModes) : latticeFullHamiltonianCLM v nu f ∈ finiteModes := by
  simp only [latticeFullHamiltonianCLM, ContinuousLinearMap.sum_apply,
    ContinuousLinearMap.add_apply, ContinuousLinearMap.mul_apply]
  refine Submodule.sum_mem _ fun i _ => Submodule.add_mem _ ?_ ?_
  · exact momentum_mem_finiteModes (latticeAdvectionCLM_mem_finiteModes v nu i hf)
  · exact latticeAdvectionCLM_mem_finiteModes v nu i (momentum_mem_finiteModes hf)
