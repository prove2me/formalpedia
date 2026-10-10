-- Prove2me | solution 1 for BookProof.QuantizationWeyl.Zgen_central
-- status  : ACCEPTED   (prove)
-- author  : @leonardopedro
-- created : 2026-10-10T10:42:15.670028+00:00
-- url     : https://prove2.me/submissions/a253aa89-9ba2-49dd-81b3-5f4c3352110b

-- Generated from ChapterQuantizationWeyl.lean — solution of BookProof.QuantizationWeyl.Zgen_central
import Mathlib
import Definitions.Def_ChapterQuantizationWeyl
open BookProof.QuantizationWeyl



open NormedSpace
open scoped Matrix


attribute [local instance] Matrix.linftyOpNormedRing Matrix.linftyOpNormedAlgebra

set_option maxHeartbeats 1000000 in
theorem solution : Xgen * Zgen = 0 ∧ Zgen * Xgen = 0 ∧ Ygen * Zgen = 0 ∧ Zgen * Ygen = 0 := by

  refine ⟨?_, ?_, ?_, ?_⟩ <;>
    · first
        | (unfold Xgen Zgen; ext i j; fin_cases i <;> fin_cases j <;>
            simp [Matrix.mul_apply, Fin.sum_univ_three])
        | (unfold Ygen Zgen; ext i j; fin_cases i <;> fin_cases j <;>
            simp [Matrix.mul_apply, Fin.sum_univ_three])
