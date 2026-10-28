-- Prove2me | solution 1 for ClusterSim.EdgeCut.eq_21
-- status  : ACCEPTED   (prove)
-- author  : @shivm
-- created : 2026-10-26T07:57:54.079295+00:00
-- url     : https://prove2.me/submissions/5df8adf1-2d58-42e1-ac63-f413ce7447a8

import Mathlib
import Definitions.Def_ClusterSim_EdgeCut_PauliData
open ClusterSim.EdgeCut Matrix

namespace Aux_CSE21
lemma hs2 : (Real.sqrt 2 : ℂ) ^ 2 = 2 := by
  rw [← Complex.ofReal_pow, Real.sq_sqrt (by norm_num)]; norm_num
lemma hs0 : (Real.sqrt 2 : ℂ) ≠ 0 := by
  intro h; have := hs2; rw [h] at this; norm_num at this
lemma p0 : proj ket0 = !![1, 0; 0, 0] := by
  ext i j; fin_cases i <;> fin_cases j <;> simp [proj, ket0, vecMulVec_apply]
lemma p1 : proj ket1 = !![0, 0; 0, 1] := by
  ext i j; fin_cases i <;> fin_cases j <;> simp [proj, ket1, vecMulVec_apply]
lemma pP : proj ketPlus = !![1/2, 1/2; 1/2, 1/2] := by
  have := hs0
  ext i j; fin_cases i <;> fin_cases j <;> simp [proj, ketPlus, vecMulVec_apply] <;>
    field_simp <;> simp [hs2]
lemma pM : proj ketMinus = !![1/2, -1/2; -1/2, 1/2] := by
  have := hs0
  ext i j; fin_cases i <;> fin_cases j <;> simp [proj, ketMinus, vecMulVec_apply] <;>
    field_simp <;> simp [hs2]
lemma pPI : proj ketPlusI = !![1/2, -Complex.I/2; Complex.I/2, 1/2] := by
  have := hs0
  ext i j; fin_cases i <;> fin_cases j <;> simp [proj, ketPlusI, vecMulVec_apply] <;>
    field_simp <;> simp [hs2]
lemma pMI : proj ketMinusI = !![1/2, Complex.I/2; -Complex.I/2, 1/2] := by
  have := hs0
  ext i j; fin_cases i <;> fin_cases j <;> simp [proj, ketMinusI, vecMulVec_apply] <;>
    field_simp <;> simp [hs2]
end Aux_CSE21

open ClusterSim.EdgeCut Aux_CSE21 in
theorem solution (A : Matrix (Fin 2) (Fin 2) ℂ) :
    A = ∑ i : Fin 8, (coef i : ℂ) • measPrep i A := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [Fin.sum_univ_eight, measPrep, coef, pauli, eigProj, p0, p1, pP, pM, pPI, pMI,
      pauliI, pauliX, pauliY, pauliZ, trace_fin_two, mul_apply, Fin.sum_univ_two]
  · ring
  · linear_combination (A 0 1 - A 1 0) / 2 * Complex.I_sq
  · linear_combination -(A 0 1 - A 1 0) / 2 * Complex.I_sq
  · ring
