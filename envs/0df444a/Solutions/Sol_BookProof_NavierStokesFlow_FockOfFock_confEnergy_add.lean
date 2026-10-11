-- Prove2me | solution 1 for BookProof.NavierStokesFlow.FockOfFock.confEnergy_add
-- status  : ACCEPTED   (prove)
-- author  : @leonardopedro
-- created : 2026-10-10T23:25:14.327984+00:00
-- url     : https://prove2.me/submissions/6ec21006-b4d1-4459-a919-d409080e1db2

-- Generated from ChapterNavierStokesFockEsa.lean — solution of BookProof.NavierStokesFlow.FockOfFock.confEnergy_add
import Mathlib
import Definitions.Def_ChapterNavierStokesFockEsa
import Definitions.Def_ChapterFockOneParticleGap
import Definitions.Def_ChapterFockSecondQuantization
import Definitions.Def_ChapterNavierStokesAffineFiberEsa
import Definitions.Def_ChapterNavierStokesFockSpace
open BookProof.NavierStokesFlow
open BookProof.NavierStokesFlow.FockOfFock



open MeasureTheory



open FullEsa LagrangianEsa

variable {M : Type*} [DecidableEq M]

set_option maxHeartbeats 1000000 in
theorem solution (ω₁ ω₂ : M → ℝ) (n : Conf M) :
    confEnergy (ω₁ + ω₂) n = confEnergy ω₁ n + confEnergy ω₂ n := by

  simp only [confEnergy, Pi.add_apply, mul_add]
  exact Finset.sum_add_distrib
