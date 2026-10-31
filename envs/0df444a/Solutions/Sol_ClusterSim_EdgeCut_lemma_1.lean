-- Prove2me | solution 1 for ClusterSim.EdgeCut.lemma_1
-- status  : ACCEPTED   (prove)
-- author  : @kmehltretter82
-- created : 2026-10-30T23:08:32.900453+00:00
-- url     : https://prove2.me/submissions/6a26e993-f912-4b02-b10d-fe35d1cd6ec8

import Mathlib.Analysis.Complex.Basic
import Mathlib.Analysis.Complex.Order
import Mathlib.Analysis.RCLike.Basic
import Definitions.Def_ClusterSim_EdgeCut_Cut
import Theorems.Thm_ClusterSim_EdgeCut_eqs_31_32

open ClusterSim.EdgeCut Matrix
open scoped ComplexOrder

private lemma hs2 : (Real.sqrt 2 : ℂ) ^ 2 = 2 := by
  rw [← Complex.ofReal_pow, Real.sq_sqrt (by norm_num)]; norm_num

private lemma hs0 : (Real.sqrt 2 : ℂ) ≠ 0 := by
  intro h; have := hs2; rw [h] at this; norm_num at this

private lemma p0 : proj ket0 = !![1, 0; 0, 0] := by
  ext i j; fin_cases i <;> fin_cases j <;> simp [proj, ket0, vecMulVec_apply]

private lemma p1 : proj ket1 = !![0, 0; 0, 1] := by
  ext i j; fin_cases i <;> fin_cases j <;> simp [proj, ket1, vecMulVec_apply]

private lemma pP : proj ketPlus = !![1/2, 1/2; 1/2, 1/2] := by
  have := hs0
  ext i j; fin_cases i <;> fin_cases j <;> simp [proj, ketPlus, vecMulVec_apply] <;>
    field_simp <;> simp [hs2]

private lemma pM : proj ketMinus = !![1/2, -1/2; -1/2, 1/2] := by
  have := hs0
  ext i j; fin_cases i <;> fin_cases j <;> simp [proj, ketMinus, vecMulVec_apply] <;>
    field_simp <;> simp [hs2]

private lemma pPI : proj ketPlusI = !![1/2, -Complex.I/2; Complex.I/2, 1/2] := by
  have := hs0
  ext i j; fin_cases i <;> fin_cases j <;> simp [proj, ketPlusI, vecMulVec_apply] <;>
    field_simp <;> simp [hs2]

private lemma pMI : proj ketMinusI = !![1/2, Complex.I/2; -Complex.I/2, 1/2] := by
  have := hs0
  ext i j; fin_cases i <;> fin_cases j <;> simp [proj, ketMinusI, vecMulVec_apply] <;>
    field_simp <;> simp [hs2]

theorem solution (G : TensorNetwork) (e : G.E) :
    value G = ∑ i : Fin 8, (coef i : ℂ) * value (cut G {e} (fun _ => i)) ∧
      ∀ i : Fin 8,
        (coef i = 1 / 2 ∨ coef i = -1 / 2) ∧
        (eigProj i).PosSemidef ∧ (eigProj i).trace = 1 ∧ eigProj i * eigProj i = eigProj i ∧
        (pauli i).IsHermitian ∧ pauli i * pauli i = 1 ∧
        pauli i * eigProj i = (2 * coef i : ℂ) • eigProj i := by
  constructor
  · rw [eqs_31_32 G {e}]
    rw [← Equiv.sum_comp (Equiv.funUnique ({e} : Finset G.E) (Fin 8)).symm]
    apply Finset.sum_congr rfl
    intro i _
    have hcoef : coefS (fun _ : ({e} : Finset G.E) => i) = coef i := by
      unfold coefS
      rw [Finset.prod_const, Finset.card_univ, Fintype.card_coe, Finset.card_singleton, pow_one]
    have huniq : ((Equiv.funUnique ({e} : Finset G.E) (Fin 8)).symm i) = (fun _ => i) := rfl
    rw [huniq, hcoef]
  · intro i
    refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
    · fin_cases i <;> simp [coef] <;> norm_num
    · fin_cases i <;> exact Matrix.posSemidef_vecMulVec_self_star _
    · fin_cases i <;> simp [eigProj, p0, p1, pP, pM, pPI, pMI, Matrix.trace_fin_two] <;> ring
    · fin_cases i <;> (ext r c; fin_cases r <;> fin_cases c <;>
        simp [eigProj, p0, p1, pP, pM, pPI, pMI, Matrix.mul_apply, Fin.sum_univ_two] <;>
        ring_nf <;> simp [Complex.I_sq] <;> ring)
    · fin_cases i <;> (ext r c; fin_cases r <;> fin_cases c <;>
        simp [pauli, pauliI, pauliX, pauliY, pauliZ, Matrix.conjTranspose_apply])
    · fin_cases i <;> (ext r c; fin_cases r <;> fin_cases c <;>
        simp [pauli, pauliI, pauliX, pauliY, pauliZ, Matrix.mul_apply, Fin.sum_univ_two,
          Matrix.one_apply] <;> ring_nf <;> simp [Complex.I_sq])
    · fin_cases i <;> (ext r c; fin_cases r <;> fin_cases c <;>
        simp [pauli, pauliI, pauliX, pauliY, pauliZ, eigProj, p0, p1, pP, pM, pPI, pMI, coef,
          Matrix.mul_apply, Fin.sum_univ_two] <;>
        ring_nf <;> simp [Complex.I_sq] <;> ring)
