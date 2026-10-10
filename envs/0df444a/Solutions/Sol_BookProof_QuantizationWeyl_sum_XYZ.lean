-- Prove2me | solution 1 for BookProof.QuantizationWeyl.sum_XYZ
-- status  : ACCEPTED   (prove)
-- author  : @leonardopedro
-- created : 2026-10-10T10:42:28.396568+00:00
-- url     : https://prove2.me/submissions/41a8ca86-4203-418f-a496-42d236eb2aad

-- Generated from ChapterQuantizationWeyl.lean — solution of BookProof.QuantizationWeyl.sum_XYZ
import Mathlib
import Definitions.Def_ChapterQuantizationWeyl
open BookProof.QuantizationWeyl



open NormedSpace
open scoped Matrix


attribute [local instance] Matrix.linftyOpNormedRing Matrix.linftyOpNormedAlgebra

set_option maxHeartbeats 1000000 in
theorem solution (a b : ℝ) :
    a • Xgen + b • Ygen + (a * b / 2) • Zgen = Ngen a b (a * b / 2) := by

  unfold Xgen Ygen Zgen Ngen; ext i j; fin_cases i <;> fin_cases j <;> simp
