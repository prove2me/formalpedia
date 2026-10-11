-- Prove2me | solution 1 for BookProof.NavierStokesFlow.FockOfFock.intervalDens_mul_extField_eq
-- status  : ACCEPTED   (prove)
-- author  : @leonardopedro
-- created : 2026-10-10T23:27:05.943008+00:00
-- url     : https://prove2.me/submissions/f41eb500-98f4-4b57-b54f-a81b91a269bd

-- Generated from ChapterNavierStokesFockEsa.lean — solution of BookProof.NavierStokesFlow.FockOfFock.intervalDens_mul_extField_eq
import Mathlib
import Definitions.Def_ChapterNavierStokesFockEsa
import Definitions.Def_ChapterNavierStokesAffineFiberEsa
import Definitions.Def_ChapterNavierStokesFockSpace
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
theorem solution (j : ℕ) :
    (fun ξ => extField ξ * intervalDens j ξ)
      = Set.indicator (Set.Ioc (j : ℝ) ((j : ℝ) + 1)) (fun ξ => ξ ^ 2) := by

  funext ξ
  by_cases hx : ξ ∈ Set.Ioc (j : ℝ) ((j : ℝ) + 1) <;>
    simp [extField, intervalDens, Set.indicator_of_mem, Set.indicator_of_notMem, hx]
