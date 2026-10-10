-- Prove2me | solution 1 for BookProof.QuantizationWeyl.sum_YZ
-- status  : ACCEPTED   (prove)
-- author  : @leonardopedro
-- created : 2026-10-10T10:42:29.628306+00:00
-- url     : https://prove2.me/submissions/8b28fef9-6e89-4ceb-be07-07536eddb1c4

-- Generated from ChapterQuantizationWeyl.lean — solution of BookProof.QuantizationWeyl.sum_YZ
import Mathlib
import Definitions.Def_ChapterQuantizationWeyl
open BookProof.QuantizationWeyl



open NormedSpace
open scoped Matrix


attribute [local instance] Matrix.linftyOpNormedRing Matrix.linftyOpNormedAlgebra

set_option maxHeartbeats 1000000 in
theorem solution (a b : ℝ) : b • Ygen + (a * b) • Zgen = Ngen 0 b (a * b) := by

  unfold Ygen Zgen Ngen; ext i j; fin_cases i <;> fin_cases j <;> simp
