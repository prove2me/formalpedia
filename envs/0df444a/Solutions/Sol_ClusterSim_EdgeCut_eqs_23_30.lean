-- Prove2me | solution 1 for ClusterSim.EdgeCut.eqs_23_30
-- status  : ACCEPTED   (prove)
-- author  : @shivm
-- created : 2026-10-26T11:34:25.773953+00:00
-- url     : https://prove2.me/submissions/ef3dd221-ad7d-461c-86b6-b42bac5bc81c

import Mathlib
import Definitions.Def_ClusterSim_EdgeCut_TensorNetwork
import Definitions.Def_ClusterSim_EdgeCut_PauliData

open Matrix

open ClusterSim.EdgeCut in
theorem solution (a b : Idx) :
    gateTensor 1 a b = ∑ i : Fin 8, (coef i : ℂ) * obsTensor (pauli i) a * stateTensor (eigProj i) b ∧
      gateTensor 1 a b = if a = b then 1 else 0 := by
  have hs : ((Real.sqrt 2 : ℝ) : ℂ) * ((Real.sqrt 2 : ℝ) : ℂ) = 2 := by
    rw [← Complex.ofReal_mul, Real.mul_self_sqrt (by norm_num)]; norm_num
  have hs2 : ((Real.sqrt 2 : ℝ) : ℂ) ^ 2 = 2 := by rw [sq, hs]
  have hs0 : ((Real.sqrt 2 : ℝ) : ℂ) ≠ 0 := by
    rw [Complex.ofReal_ne_zero]; positivity
  have p0 : proj ket0 = !![1, 0; 0, 0] := by
    ext i j; fin_cases i <;> fin_cases j <;> simp [proj, ket0, vecMulVec_apply]
  have p1 : proj ket1 = !![0, 0; 0, 1] := by
    ext i j; fin_cases i <;> fin_cases j <;> simp [proj, ket1, vecMulVec_apply]
  have pp : proj ketPlus = !![1/2, 1/2; 1/2, 1/2] := by
    ext i j; fin_cases i <;> fin_cases j <;> simp [proj, ketPlus, vecMulVec_apply] <;>
      ring_nf <;> simp [inv_pow, hs2, Complex.I_sq] <;> ring_nf
  have pm : proj ketMinus = !![1/2, -1/2; -1/2, 1/2] := by
    ext i j; fin_cases i <;> fin_cases j <;> simp [proj, ketMinus, vecMulVec_apply] <;>
      ring_nf <;> simp [inv_pow, hs2, Complex.I_sq] <;> ring_nf
  have ppi : proj ketPlusI = !![1/2, -Complex.I/2; Complex.I/2, 1/2] := by
    ext i j; fin_cases i <;> fin_cases j <;> simp [proj, ketPlusI, vecMulVec_apply] <;>
      ring_nf <;> simp [inv_pow, hs2, Complex.I_sq] <;> ring_nf
  have pmi : proj ketMinusI = !![1/2, Complex.I/2; -Complex.I/2, 1/2] := by
    ext i j; fin_cases i <;> fin_cases j <;> simp [proj, ketMinusI, vecMulVec_apply] <;>
      ring_nf <;> simp [inv_pow, hs2, Complex.I_sq] <;> ring_nf
  obtain ⟨a1, a2⟩ := a
  obtain ⟨b1, b2⟩ := b
  fin_cases a1 <;> fin_cases a2 <;> fin_cases b1 <;> fin_cases b2 <;>
    simp [gateTensor, obsTensor, stateTensor, M, trace_fin_two, Matrix.mul_apply, Fin.sum_univ_two,
      Matrix.single_apply, Fin.sum_univ_eight, coef, pauli, eigProj, p0, p1, pp, pm, ppi, pmi,
      pauliI, pauliX, pauliY, pauliZ] <;> ring_nf <;> simp [Complex.I_sq] <;> ring_nf
