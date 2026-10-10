-- Prove2me | solution 1 for BookProof.QuantizationWeyl.Ngen_eq
-- status  : ACCEPTED   (prove)
-- author  : @leonardopedro
-- created : 2026-10-10T10:42:21.11249+00:00
-- url     : https://prove2.me/submissions/1936f644-cf4c-4fcc-83b2-9fa611dd52fd

-- Generated from ChapterQuantizationWeyl.lean — solution of BookProof.QuantizationWeyl.Ngen_eq
import Mathlib
import Definitions.Def_ChapterQuantizationWeyl
open BookProof.QuantizationWeyl



open NormedSpace
open scoped Matrix


attribute [local instance] Matrix.linftyOpNormedRing Matrix.linftyOpNormedAlgebra

set_option maxHeartbeats 1000000 in
theorem solution (a b c : ℝ) : a • Xgen + b • Ygen + c • Zgen = Ngen a b c := by

  unfold Xgen Ygen Zgen Ngen; ext i j; fin_cases i <;> fin_cases j <;> simp
