-- Prove2me | solution 1 for BookProof.QuantizationWeyl.smul_Ygen
-- status  : ACCEPTED   (prove)
-- author  : @leonardopedro
-- created : 2026-10-10T10:42:27.242651+00:00
-- url     : https://prove2.me/submissions/5dcc2485-5d46-4d51-bab4-023480e27423

-- Generated from ChapterQuantizationWeyl.lean — solution of BookProof.QuantizationWeyl.smul_Ygen
import Mathlib
import Definitions.Def_ChapterQuantizationWeyl
open BookProof.QuantizationWeyl



open NormedSpace
open scoped Matrix


attribute [local instance] Matrix.linftyOpNormedRing Matrix.linftyOpNormedAlgebra

set_option maxHeartbeats 1000000 in
theorem solution (b : ℝ) : b • Ygen = Ngen 0 b 0 := by

  unfold Ygen Ngen; ext i j; fin_cases i <;> fin_cases j <;> simp
