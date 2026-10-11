-- Prove2me | solution 1 for BookProof.NavierStokesFlow.FockOfFock.intervalDens_integrable
-- status  : ACCEPTED   (prove)
-- author  : @leonardopedro
-- created : 2026-10-10T23:27:07.132249+00:00
-- url     : https://prove2.me/submissions/593f1f4f-5bad-4429-8755-d1fc7c55780c

-- Generated from ChapterNavierStokesFockEsa.lean — solution of BookProof.NavierStokesFlow.FockOfFock.intervalDens_integrable
import Mathlib
import Definitions.Def_ChapterNavierStokesFockEsa
import Theorems.Thm_BookProof_NavierStokesFlow_FockOfFock_intervalDens_mul_extField_eq
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
    Integrable (fun ξ => extField ξ * intervalDens j ξ) volume := by

  rw [intervalDens_mul_extField_eq, integrable_indicator_iff measurableSet_Ioc]
  exact (intervalIntegrable_iff_integrableOn_Ioc_of_le (by linarith)).1
    ((continuous_pow 2).intervalIntegrable _ _)
