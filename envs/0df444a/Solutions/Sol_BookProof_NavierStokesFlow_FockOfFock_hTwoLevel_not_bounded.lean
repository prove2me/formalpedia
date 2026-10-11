-- Prove2me | solution 1 for BookProof.NavierStokesFlow.FockOfFock.hTwoLevel_not_bounded
-- status  : ACCEPTED   (prove)
-- author  : @leonardopedro
-- created : 2026-10-10T23:26:34.526704+00:00
-- url     : https://prove2.me/submissions/ccb34e17-1b35-47c3-9bd1-143d57935dcf

-- Generated from ChapterNavierStokesFockEsa.lean — solution of BookProof.NavierStokesFlow.FockOfFock.hTwoLevel_not_bounded
import Mathlib
import Definitions.Def_ChapterNavierStokesFockEsa
import Theorems.Thm_BookProof_NavierStokesFlow_FockOfFock_confEnergy_zero
import Theorems.Thm_BookProof_NavierStokesFlow_FockOfFock_dGamma_not_bounded
import Definitions.Def_ChapterFockOneParticleGap
import Definitions.Def_ChapterFockSecondQuantization
import Definitions.Def_ChapterNavierStokesFockSpace
import Definitions.Def_ChapterNavierStokesAffineFiberEsa
open BookProof.NavierStokesFlow
open BookProof.NavierStokesFlow.FockOfFock



open MeasureTheory



open FullEsa LagrangianEsa

variable {M : Type*} [DecidableEq M]
variable {M : Type*} [DecidableEq M] {Ω : Type*} [MeasurableSpace Ω]
variable {J K : Type*} [DecidableEq J] [DecidableEq K]

set_option maxHeartbeats 1000000 in
theorem solution (ext : J → ℝ) (eps : K → ℝ) (hext : ∀ C : ℝ, ∃ j, C < |ext j|) :
    ¬ ∃ C : ℝ, ∀ f : FockOfFockDom J K, ‖hTwoLevel ext eps f‖ ≤ C * ‖f‖ := by

  refine dGamma_not_bounded _ fun C => ?_
  obtain ⟨j, hj⟩ := hext C
  exact ⟨(j, 0), by simpa [twoLevelSymbol, confEnergy_zero] using hj⟩
