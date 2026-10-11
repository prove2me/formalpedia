-- Prove2me | solution 1 for BookProof.NavierStokesFlow.FullEsa.latticeFullData_advection_apply
-- status  : ACCEPTED   (prove)
-- author  : @leonardopedro
-- created : 2026-10-11T08:19:44.905633+00:00
-- url     : https://prove2.me/submissions/6d788bd2-0681-4288-bb07-aa0591be9120

-- Generated from ChapterNavierStokesFullEsa.lean — solution of BookProof.NavierStokesFlow.FullEsa.latticeFullData_advection_apply
import Mathlib
import Definitions.Def_ChapterNavierStokesFullEsa
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

theorem solution (v : Fin 15 → LinfZ) (nu : ℝ) (i : Fin 3)
    (x : (latticeFullData v nu).D) :
    ((latticeFullData v nu).advection i x : L2Z) = latticeAdvectionCLM v nu i (x : L2Z) := by
  exact rfl
