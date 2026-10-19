-- Prove2me | solution 1 for BookProof.NavierStokesFlow.FockLagrangian.momFock_core_ne_top
-- status  : ACCEPTED   (prove)
-- author  : @leonardopedro
-- created : 2026-10-18T21:07:09.542221+00:00
-- url     : https://prove2.me/submissions/54334fb4-c5d3-4c62-9315-4dfcfca9d1c7

-- Generated from ChapterNavierStokesFockParcels.lean — solution of BookProof.NavierStokesFlow.FockLagrangian.momFock_core_ne_top
import Mathlib
import Definitions.Def_ChapterNavierStokesFockParcels
import Theorems.Thm_BookProof_NavierStokesFlow_FockLagrangian_tailState_not_mem_core
import Definitions.Def_ChapterNavierStokesAffineFiberEsa
import Definitions.Def_ChapterNavierStokesFockLagrangian
open BookProof.NavierStokesFlow
open BookProof.NavierStokesFlow.FockLagrangian



open MeasureTheory



open FullEsa FockContinuum

variable {Ω : Type*} [MeasurableSpace Ω]

set_option maxHeartbeats 1000000 in
theorem solution : momFock.core ≠ ⊤ :=
  fun h =>
    tailState_not_mem_core (h ▸ Submodule.mem_top)
