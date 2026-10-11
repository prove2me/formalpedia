-- Prove2me | solution 1 for BookProof.NavierStokesFlow.FockOfFock.hFockLag_hasZeroDeficiencyOn
-- status  : ACCEPTED   (prove)
-- author  : @leonardopedro
-- created : 2026-10-10T23:26:35.655165+00:00
-- url     : https://prove2.me/submissions/79b7bce2-94d5-4e7c-bc36-2d438e605087

-- Generated from ChapterNavierStokesFockEsa.lean — solution of BookProof.NavierStokesFlow.FockOfFock.hFockLag_hasZeroDeficiencyOn
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

set_option maxHeartbeats 1000000 in
theorem solution (nu : ℝ) (p q dr : Fin 3 → M → ℝ) (force : Fin 3 → ℝ)
    (cst : M → ℝ) :
    HasZeroDeficiencyOn (FockDom M) (hFockLag nu p q dr force cst) := dGamma_hasZeroDeficiencyOn _
