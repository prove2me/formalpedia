-- Prove2me | solution 1 for BookProof.NavierStokesFlow.FockLagrangian.vacState_coeFn
-- status  : ACCEPTED   (prove)
-- author  : @leonardopedro
-- created : 2026-10-18T21:09:49.108375+00:00
-- url     : https://prove2.me/submissions/3c605d5e-1d7e-4a10-8c2c-8904a483836e

-- Generated from ChapterNavierStokesFockParcels.lean — solution of BookProof.NavierStokesFlow.FockLagrangian.vacState_coeFn
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
    ((vacState : Lp ℂ 2 fockR) : ParcelConf ℝ → ℂ)
      =ᵐ[fockR] vacSet.indicator (fun _ => (1 : ℂ)) := MemLp.coeFn_toLp _
