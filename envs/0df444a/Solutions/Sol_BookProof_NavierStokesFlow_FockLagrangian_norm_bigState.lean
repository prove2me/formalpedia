-- Prove2me | solution 1 for BookProof.NavierStokesFlow.FockLagrangian.norm_bigState
-- status  : ACCEPTED   (prove)
-- author  : @leonardopedro
-- created : 2026-10-18T21:03:34.433985+00:00
-- url     : https://prove2.me/submissions/1ac12753-8e91-4c0c-945f-5419b8c5fadb

-- Generated from ChapterNavierStokesFockParcels.lean — solution of BookProof.NavierStokesFlow.FockLagrangian.norm_bigState
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
theorem solution (K : ℝ) : ‖bigState K‖ = 1 := by

  rw [bigState, Lp.norm_toLp,
    eLpNorm_indicator_const (bigSet_measurable K) (by norm_num) (by norm_num),
    fockMeasure_bigSet]
  simp
