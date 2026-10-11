-- Prove2me | solution 1 for BookProof.NavierStokesFlow.FockOfFock.lagrangianFock_not_bounded
-- status  : ACCEPTED   (prove)
-- author  : @leonardopedro
-- created : 2026-10-10T23:26:36.884984+00:00
-- url     : https://prove2.me/submissions/232ab78e-5dd8-4dfc-a3ae-57e3fd73a935

-- Generated from ChapterNavierStokesFockEsa.lean — solution of BookProof.NavierStokesFlow.FockOfFock.lagrangianFock_not_bounded
import Mathlib
import Definitions.Def_ChapterNavierStokesFockEsa
import Theorems.Thm_BookProof_NavierStokesFlow_FockOfFock_dGamma_not_bounded
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
theorem solution (nu : ℝ) (p q dr : Fin 3 → M → ℝ) (force : Fin 3 → ℝ)
    (cst : M → ℝ) (h : ∀ C : ℝ, ∃ m, C < |lagSymbol nu p q dr force cst m|) :
    ¬ ((∃ C : ℝ, ∀ f : FockDom M, ‖hFockLag nu p q dr force cst f‖ ≤ C * ‖f‖)) := dGamma_not_bounded _ h
