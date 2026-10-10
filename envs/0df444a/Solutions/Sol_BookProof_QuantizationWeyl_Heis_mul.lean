-- Prove2me | solution 1 for BookProof.QuantizationWeyl.Heis_mul
-- status  : ACCEPTED   (prove)
-- author  : @leonardopedro
-- created : 2026-10-10T10:42:19.820727+00:00
-- url     : https://prove2.me/submissions/86bb2c22-e6af-4aa8-974a-991da1e3287c

-- Generated from ChapterQuantizationWeyl.lean — solution of BookProof.QuantizationWeyl.Heis_mul
import Mathlib
import Definitions.Def_ChapterQuantizationWeyl
open BookProof.QuantizationWeyl



open NormedSpace
open scoped Matrix


attribute [local instance] Matrix.linftyOpNormedRing Matrix.linftyOpNormedAlgebra

set_option maxHeartbeats 1000000 in
theorem solution (a b c a' b' c' : ℝ) :
    Heis a b c * Heis a' b' c' = Heis (a + a') (b + b') (c + c' + a * b') := by

  unfold Heis; ext i j; fin_cases i <;> fin_cases j <;>
    simp [Matrix.mul_apply, Fin.sum_univ_three] <;> ring
