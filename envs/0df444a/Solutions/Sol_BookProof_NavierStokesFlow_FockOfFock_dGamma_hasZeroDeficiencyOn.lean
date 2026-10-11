-- Prove2me | solution 1 for BookProof.NavierStokesFlow.FockOfFock.dGamma_hasZeroDeficiencyOn
-- status  : ACCEPTED   (prove)
-- author  : @leonardopedro
-- created : 2026-10-10T23:25:15.557129+00:00
-- url     : https://prove2.me/submissions/486c2d40-1b09-4712-951d-c42bed7b0d5c

-- Generated from ChapterNavierStokesFockEsa.lean — solution of BookProof.NavierStokesFlow.FockOfFock.dGamma_hasZeroDeficiencyOn
import Mathlib
import Definitions.Def_ChapterNavierStokesFockEsa
import Theorems.Thm_BookProof_NavierStokesFlow_FockOfFock_lpDiag_hasZeroDeficiencyOn
import Definitions.Def_ChapterFockOneParticleGap
import Definitions.Def_ChapterFockSecondQuantization
import Definitions.Def_ChapterNavierStokesFlow
import Definitions.Def_ChapterNavierStokesFockSpace
import Definitions.Def_ChapterNavierStokesAffineFiberEsa
open BookProof.NavierStokesFlow
open BookProof.NavierStokesFlow.FockOfFock



open MeasureTheory



open FullEsa LagrangianEsa

variable {M : Type*} [DecidableEq M]

set_option maxHeartbeats 1000000 in
theorem solution (ω : M → ℝ) :
    HasZeroDeficiencyOn (FockDom M) (dGamma ω) := lpDiag_hasZeroDeficiencyOn _
