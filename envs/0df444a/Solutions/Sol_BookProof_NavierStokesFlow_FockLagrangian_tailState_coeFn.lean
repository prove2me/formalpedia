-- Prove2me | solution 1 for BookProof.NavierStokesFlow.FockLagrangian.tailState_coeFn
-- status  : ACCEPTED   (prove)
-- author  : @leonardopedro
-- created : 2026-10-18T21:05:08.56099+00:00
-- url     : https://prove2.me/submissions/e5736bd6-4b58-49ba-bcd0-45d5a1c44e25

-- Generated from ChapterNavierStokesFockParcels.lean — solution of BookProof.NavierStokesFlow.FockLagrangian.tailState_coeFn
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
theorem solution :
    ((tailState : Lp ℂ 2 fockR) : ParcelConf ℝ → ℂ)
      =ᵐ[fockR] tailFockSet.indicator (fun _ => (1 : ℂ)) := MemLp.coeFn_toLp _
