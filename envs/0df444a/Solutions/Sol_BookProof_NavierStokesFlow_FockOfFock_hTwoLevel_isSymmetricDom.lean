-- Prove2me | solution 1 for BookProof.NavierStokesFlow.FockOfFock.hTwoLevel_isSymmetricDom
-- status  : ACCEPTED   (prove)
-- author  : @leonardopedro
-- created : 2026-10-11T17:17:03.318966+00:00
-- url     : https://prove2.me/submissions/05818f90-5e34-4997-a2c7-da7d703b8c8e

-- Generated from ChapterNavierStokesFockEsa.lean — solution of BookProof.NavierStokesFlow.FockOfFock.hTwoLevel_isSymmetricDom
import Mathlib
import Definitions.Def_ChapterNavierStokesFockEsa
import Definitions.Def_ChapterFockSecondQuantization
import Definitions.Def_ChapterNavierStokesFockSpace
import Definitions.Def_ChapterNavierStokesFullEsa
import Definitions.Def_ChapterNavierStokesAffineFiberEsa
open BookProof.NavierStokesFlow
open BookProof.NavierStokesFlow.FockOfFock



open MeasureTheory



open FullEsa LagrangianEsa

variable {M : Type*} [DecidableEq M]
variable {M : Type*} [DecidableEq M] {Ω : Type*} [MeasurableSpace Ω]
variable {J K : Type*} [DecidableEq J] [DecidableEq K]

set_option maxHeartbeats 1000000 in
omit [DecidableEq J] [DecidableEq K] in
theorem solution (ext : J → ℝ) (eps : K → ℝ) :
    IsSymmetricDom (hTwoLevel ext eps) := dGamma_isSymmetricDom _
