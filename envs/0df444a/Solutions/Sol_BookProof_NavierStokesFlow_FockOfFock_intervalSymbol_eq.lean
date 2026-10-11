-- Prove2me | solution 1 for BookProof.NavierStokesFlow.FockOfFock.intervalSymbol_eq
-- status  : ACCEPTED   (prove)
-- author  : @leonardopedro
-- created : 2026-10-10T23:27:21.697012+00:00
-- url     : https://prove2.me/submissions/d32e6fe8-9989-487a-bdef-87b655efdb2c

-- Generated from ChapterNavierStokesFockEsa.lean — solution of BookProof.NavierStokesFlow.FockOfFock.intervalSymbol_eq
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
    symbolOfIntegral volume extField intervalDens j = (((j : ℝ) + 1) ^ 3 - (j : ℝ) ^ 3) / 3 := by

  rw [symbolOfIntegral, intervalDens_mul_extField_eq, integral_indicator measurableSet_Ioc,
    ← intervalIntegral.integral_of_le (by linarith : (j : ℝ) ≤ (j : ℝ) + 1), integral_pow]
  ring
