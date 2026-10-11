-- Prove2me | solution 1 for BookProof.NavierStokesFlow.FullEsa.latticeAdvectionCLM_mem_finiteModes
-- status  : ACCEPTED   (prove)
-- author  : @leonardopedro
-- created : 2026-10-11T08:19:41.543776+00:00
-- url     : https://prove2.me/submissions/920c70c2-51f8-4d4b-a0cf-e3ec77f63d8b

-- Generated from ChapterNavierStokesFullEsa.lean — solution of BookProof.NavierStokesFlow.FullEsa.latticeAdvectionCLM_mem_finiteModes
import Mathlib
import Definitions.Def_ChapterNavierStokesFullEsa
import Definitions.Def_ChapterNavierStokesEsa
import Definitions.Def_ChapterContinuityUnitary
import Definitions.Def_ChapterContinuityUnitaryInfinite
import Definitions.Def_ChapterNavierStokesFlow
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

theorem solution (v : Fin 15 → LinfZ) (nu : ℝ) (i : Fin 3)
    {f : L2Z} (hf : f ∈ finiteModes) : latticeAdvectionCLM v nu i f ∈ finiteModes := by
  simp only [latticeAdvectionCLM, ContinuousLinearMap.sub_apply, ContinuousLinearMap.sum_apply,
    ContinuousLinearMap.smul_apply, ContinuousLinearMap.mul_apply]
  refine Submodule.sub_mem _ (Submodule.sum_mem _ fun j _ => ?_)
    (Submodule.smul_mem _ _ (velocityOp_mem_finiteModes _ hf))
  exact velocityOp_mem_finiteModes _ (velocityOp_mem_finiteModes _ hf)
