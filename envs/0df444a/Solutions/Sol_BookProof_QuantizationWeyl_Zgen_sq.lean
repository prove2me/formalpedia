-- Prove2me | solution 1 for BookProof.QuantizationWeyl.Zgen_sq
-- status  : ACCEPTED   (prove)
-- author  : @leonardopedro
-- created : 2026-10-10T10:42:16.932872+00:00
-- url     : https://prove2.me/submissions/51a25bcf-d0fb-4c46-8022-683342fb4454

-- Generated from ChapterQuantizationWeyl.lean — solution of BookProof.QuantizationWeyl.Zgen_sq
import Mathlib
import Definitions.Def_ChapterQuantizationWeyl
open BookProof.QuantizationWeyl



open NormedSpace
open scoped Matrix


attribute [local instance] Matrix.linftyOpNormedRing Matrix.linftyOpNormedAlgebra

set_option maxHeartbeats 1000000 in
theorem solution : Zgen ^ 2 = 0 := by

  unfold Zgen; ext i j; fin_cases i <;> fin_cases j <;>
    simp [pow_succ, Matrix.mul_apply, Fin.sum_univ_three]
