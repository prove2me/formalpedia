-- Prove2me | solution 1 for BookProof.NavierStokesFlow.FockOfFock.intervalTwoLevel_hasZeroDeficiencyOn
-- status  : ACCEPTED   (prove)
-- author  : @leonardopedro
-- created : 2026-10-10T23:39:12.713298+00:00
-- url     : https://prove2.me/submissions/162292c1-c61f-4b6f-9e96-e96e69d14533

-- Generated from ChapterNavierStokesFockEsa.lean — solution of BookProof.NavierStokesFlow.FockOfFock.intervalTwoLevel_hasZeroDeficiencyOn
import Mathlib
import Definitions.Def_ChapterNavierStokesFockEsa
import Theorems.Thm_BookProof_NavierStokesFlow_FockOfFock_dGamma_hasZeroDeficiencyOn
import Definitions.Def_ChapterFockSecondQuantization
import Definitions.Def_ChapterNavierStokesFlow
import Definitions.Def_ChapterNavierStokesFockSpace
import Definitions.Def_ChapterNavierStokesAffineFiberEsa
open BookProof.NavierStokesFlow
open BookProof.NavierStokesFlow.FockOfFock



open MeasureTheory



open FullEsa LagrangianEsa

variable {M : Type*} [DecidableEq M]
variable {M : Type*} [DecidableEq M] {Ω : Type*} [MeasurableSpace Ω]
variable {J K : Type*} [DecidableEq J] [DecidableEq K]
variable {F : Type*} [NormedAddCommGroup F] [InnerProductSpace ℂ F]
variable {K : Type*} [DecidableEq K]

set_option maxHeartbeats 1000000 in
theorem solution (eps : K → ℝ) :
    HasZeroDeficiencyOn (FockOfFockDom ℕ K) (dGamma (intervalTwoLevelSymbol eps)) := dGamma_hasZeroDeficiencyOn _
