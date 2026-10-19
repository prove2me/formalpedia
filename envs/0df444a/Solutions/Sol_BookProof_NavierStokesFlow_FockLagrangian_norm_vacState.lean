-- Prove2me | solution 1 for BookProof.NavierStokesFlow.FockLagrangian.norm_vacState
-- status  : ACCEPTED   (prove)
-- author  : @leonardopedro
-- created : 2026-10-18T21:38:35.107114+00:00
-- url     : https://prove2.me/submissions/9fa3bacf-8d39-4e66-bf32-c16a54435a15

-- Generated from ChapterNavierStokesFockParcels.lean — solution of BookProof.NavierStokesFlow.FockLagrangian.norm_vacState
import Mathlib
import Definitions.Def_ChapterNavierStokesFockParcels
import Definitions.Def_ChapterNavierStokesAffineFiberEsa
import Definitions.Def_ChapterNavierStokesFockLagrangian
open BookProof.NavierStokesFlow
open BookProof.NavierStokesFlow.FockLagrangian



open MeasureTheory



open FullEsa FockContinuum

variable {Ω : Type*} [MeasurableSpace Ω]

set_option maxHeartbeats 1000000 in
theorem solution : ‖vacState‖ = 1 := by

  rw [vacState, Lp.norm_toLp,
    eLpNorm_indicator_const vacSet_measurable (by norm_num) (by norm_num), fockMeasure_vacSet]
  simp
