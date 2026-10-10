-- Prove2me | solution 1 for BookProof.QuantizationWeyl.smul_Xgen
-- status  : ACCEPTED   (prove)
-- author  : @leonardopedro
-- created : 2026-10-10T10:42:26.09137+00:00
-- url     : https://prove2.me/submissions/7bf8b232-52d3-499c-ae20-1e6585a40423

-- Generated from ChapterQuantizationWeyl.lean — solution of BookProof.QuantizationWeyl.smul_Xgen
import Mathlib
import Definitions.Def_ChapterQuantizationWeyl
open BookProof.QuantizationWeyl



open NormedSpace
open scoped Matrix


attribute [local instance] Matrix.linftyOpNormedRing Matrix.linftyOpNormedAlgebra

set_option maxHeartbeats 1000000 in
theorem solution (a : ℝ) : a • Xgen = Ngen a 0 0 := by

  unfold Xgen Ngen; ext i j; fin_cases i <;> fin_cases j <;> simp
