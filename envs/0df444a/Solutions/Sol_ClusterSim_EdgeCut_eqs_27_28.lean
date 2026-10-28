-- Prove2me | solution 1 for ClusterSim.EdgeCut.eqs_27_28
-- status  : ACCEPTED   (prove)
-- author  : @shivm
-- created : 2026-10-26T11:32:02.524706+00:00
-- url     : https://prove2.me/submissions/be67a49c-2352-4aee-8e06-6491278027f1

import Mathlib
import Definitions.Def_ClusterSim_EdgeCut_PauliData

open Matrix Kronecker

open ClusterSim.EdgeCut in
theorem solution :
    (∑ i : Fin 8, (coef i : ℂ) • (pauli i ⊗ₖ eigProj i)) =
        (1 / 2 : ℂ) • (pauliI ⊗ₖ pauliI + pauliX ⊗ₖ pauliX + pauliY ⊗ₖ pauliY + pauliZ ⊗ₖ pauliZ) ∧
      (1 / 2 : ℂ) • (pauliI ⊗ₖ pauliI + pauliX ⊗ₖ pauliX + pauliY ⊗ₖ pauliY + pauliZ ⊗ₖ pauliZ) =
        Matrix.of (fun (x y : Fin 2 × Fin 2) => if x.1 = y.2 ∧ x.2 = y.1 then (1 : ℂ) else 0) := by
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
  constructor
  · ext ⟨a, b⟩ ⟨c, d⟩
    fin_cases a <;> fin_cases b <;> fin_cases c <;> fin_cases d <;>
      simp [Fin.sum_univ_eight, coef, pauli, eigProj, p0, p1, pp, pm, ppi, pmi,
        kroneckerMap_apply, pauliI, pauliX, pauliY, pauliZ] <;> ring_nf <;>
      simp [Complex.I_sq] <;> ring_nf
  · ext ⟨a, b⟩ ⟨c, d⟩
    fin_cases a <;> fin_cases b <;> fin_cases c <;> fin_cases d <;>
      simp [kroneckerMap_apply, pauliI, pauliX, pauliY, pauliZ] <;> ring_nf <;>
      simp [Complex.I_sq] <;> ring_nf
