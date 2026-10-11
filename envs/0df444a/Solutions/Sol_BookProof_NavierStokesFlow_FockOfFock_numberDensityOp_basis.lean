-- Prove2me | solution 1 for BookProof.NavierStokesFlow.FockOfFock.numberDensityOp_basis
-- status  : ACCEPTED   (prove)
-- author  : @leonardopedro
-- created : 2026-10-10T23:26:02.4484+00:00
-- url     : https://prove2.me/submissions/313114c5-f345-414b-9c6f-e66bb47f2c5e

-- Generated from ChapterNavierStokesFockEsa.lean — solution of BookProof.NavierStokesFlow.FockOfFock.numberDensityOp_basis
import Mathlib
import Definitions.Def_ChapterNavierStokesFockEsa
import Theorems.Thm_BookProof_NavierStokesFlow_FockOfFock_lpDiag_basis
import Definitions.Def_ChapterFockSecondQuantization
import Definitions.Def_ChapterNavierStokesFockSpace
import Definitions.Def_ChapterNavierStokesAffineFiberEsa
open BookProof.NavierStokesFlow
open BookProof.NavierStokesFlow.FockOfFock



open MeasureTheory



open FullEsa LagrangianEsa

variable {M : Type*} [DecidableEq M]
variable {M : Type*} [DecidableEq M] {Ω : Type*} [MeasurableSpace Ω]

set_option maxHeartbeats 1000000 in
theorem solution (dens : M → Ω → ℝ) (ξ : Ω) (n : Conf M) :
    numberDensityOp dens ξ (fockBasis n) = ((confDensity dens n ξ : ℝ) : ℂ) • fockBasis n := lpDiag_basis _ n
