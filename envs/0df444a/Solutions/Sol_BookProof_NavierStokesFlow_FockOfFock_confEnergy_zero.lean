-- Prove2me | solution 1 for BookProof.NavierStokesFlow.FockOfFock.confEnergy_zero
-- status  : ACCEPTED   (prove)
-- author  : @leonardopedro
-- created : 2026-10-10T23:24:56.939577+00:00
-- url     : https://prove2.me/submissions/56cd6feb-ef80-46ca-b110-0c5916b6f541

-- Generated from ChapterNavierStokesFockEsa.lean — solution of BookProof.NavierStokesFlow.FockOfFock.confEnergy_zero
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
theorem solution (ω : M → ℝ) : confEnergy ω (0 : Conf M) = 0 := by

  simp [confEnergy]
