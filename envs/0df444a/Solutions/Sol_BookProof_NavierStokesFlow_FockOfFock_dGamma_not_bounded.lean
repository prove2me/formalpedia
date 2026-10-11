-- Prove2me | solution 1 for BookProof.NavierStokesFlow.FockOfFock.dGamma_not_bounded
-- status  : ACCEPTED   (prove)
-- author  : @leonardopedro
-- created : 2026-10-10T23:25:16.631988+00:00
-- url     : https://prove2.me/submissions/81522400-dced-4e50-bd7d-46a604f61abe

-- Generated from ChapterNavierStokesFockEsa.lean — solution of BookProof.NavierStokesFlow.FockOfFock.dGamma_not_bounded
import Mathlib
import Definitions.Def_ChapterNavierStokesFockEsa
import Theorems.Thm_BookProof_NavierStokesFlow_FockOfFock_lpDiag_not_bounded
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
theorem solution (ω : M → ℝ) (hω : ∀ C : ℝ, ∃ m, C < |ω m|) :
    ¬ ∃ C : ℝ, ∀ f : FockDom M, ‖dGamma ω f‖ ≤ C * ‖f‖ := by

  refine lpDiag_not_bounded _ fun C => ?_
  obtain ⟨m, hm⟩ := hω C
  refine ⟨Finsupp.single m 1, ?_⟩
  have : confEnergy ω (Finsupp.single m 1) = ω m := by
    simp [confEnergy, Finsupp.support_single_ne_zero _ (one_ne_zero)]
  rwa [this]
