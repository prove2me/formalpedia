-- Prove2me | solution 1 for BookProof.NavierStokesFlow.FockOfFock.dGamma_basis
-- status  : ACCEPTED   (prove)
-- author  : @leonardopedro
-- created : 2026-10-10T23:25:13.210896+00:00
-- url     : https://prove2.me/submissions/255d3cfb-07e4-4069-9c24-0477f0ed43e6

-- Generated from ChapterNavierStokesFockEsa.lean — solution of BookProof.NavierStokesFlow.FockOfFock.dGamma_basis
import Mathlib
import Definitions.Def_ChapterNavierStokesFockEsa
import Theorems.Thm_BookProof_NavierStokesFlow_FockOfFock_lpDiag_basis
import Definitions.Def_ChapterFockOneParticleGap
import Definitions.Def_ChapterFockSecondQuantization
import Definitions.Def_ChapterNavierStokesFockSpace
import Definitions.Def_ChapterNavierStokesAffineFiberEsa
open BookProof.NavierStokesFlow
open BookProof.NavierStokesFlow.FockOfFock



open MeasureTheory



open FullEsa LagrangianEsa

variable {M : Type*} [DecidableEq M]

set_option maxHeartbeats 1000000 in
theorem solution (ω : M → ℝ) (n : Conf M) :
    dGamma ω (fockBasis n) = ((confEnergy ω n : ℝ) : ℂ) • fockBasis n := lpDiag_basis _ n
