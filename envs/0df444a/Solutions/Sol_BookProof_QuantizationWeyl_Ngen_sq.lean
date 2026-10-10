-- Prove2me | solution 1 for BookProof.QuantizationWeyl.Ngen_sq
-- status  : ACCEPTED   (prove)
-- author  : @leonardopedro
-- created : 2026-10-10T10:42:23.620582+00:00
-- url     : https://prove2.me/submissions/c72a886e-62c0-4114-abbf-40c6779e4691

-- Generated from ChapterQuantizationWeyl.lean — solution of BookProof.QuantizationWeyl.Ngen_sq
import Mathlib
import Definitions.Def_ChapterQuantizationWeyl
open BookProof.QuantizationWeyl



open NormedSpace
open scoped Matrix


attribute [local instance] Matrix.linftyOpNormedRing Matrix.linftyOpNormedAlgebra

set_option maxHeartbeats 1000000 in
theorem solution (a b c : ℝ) : (Ngen a b c) ^ 2 = (a * b) • Zgen := by

  unfold Ngen Zgen; ext i j; fin_cases i <;> fin_cases j <;>
    simp [pow_succ, Matrix.mul_apply, Fin.sum_univ_three]
