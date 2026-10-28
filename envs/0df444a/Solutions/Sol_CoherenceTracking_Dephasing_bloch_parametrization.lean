-- Prove2me | solution 1 for CoherenceTracking.Dephasing.bloch_parametrization
-- status  : ACCEPTED   (prove)
-- author  : @mrfancypants
-- created : 2026-10-27T02:51:24.536978+00:00
-- url     : https://prove2.me/submissions/be9ea3fe-3e2c-44bb-933e-6c311b9a0acd

import Mathlib
import Definitions.Def_CoherenceTracking_Dephasing_Model

namespace CoherenceTracking.Dephasing
open Matrix Complex

lemma pauli0 : pauli 0 = !![0, 1; 1, 0] := rfl
lemma pauli1 : pauli 1 = !![0, -Complex.I; Complex.I, 0] := rfl
lemma pauli2 : pauli 2 = !![1, 0; 0, -1] := rfl

lemma bv0 (ρ : Qmat) : blochVec ρ 0 = (ρ 0 1 + ρ 1 0).re := by
  simp [blochVec, pauli0, Matrix.trace, Matrix.mul_apply, Fin.sum_univ_two]
lemma bv1 (ρ : Qmat) : blochVec ρ 1 = (ρ 1 0).im - (ρ 0 1).im := by
  simp [blochVec, pauli1, Matrix.trace, Matrix.mul_apply, Fin.sum_univ_two]
  ring_nf
lemma bv2 (ρ : Qmat) : blochVec ρ 2 = (ρ 0 0).re - (ρ 1 1).re := by
  simp [blochVec, pauli2, Matrix.trace, Matrix.mul_apply, Fin.sum_univ_two]
  ring_nf

lemma bs00 (v : BVec) : blochState v 0 0 = (1 + (v 2 : ℂ)) / 2 := by
  simp [blochState, pauli0, pauli1, pauli2, Fin.sum_univ_three]
  ring
lemma bs11 (v : BVec) : blochState v 1 1 = (1 - (v 2 : ℂ)) / 2 := by
  simp [blochState, pauli0, pauli1, pauli2, Fin.sum_univ_three]
  ring
lemma bs01 (v : BVec) : blochState v 0 1 = ((v 0 : ℂ) - Complex.I * (v 1 : ℂ)) / 2 := by
  simp [blochState, pauli0, pauli1, pauli2, Fin.sum_univ_three]
  ring
lemma bs10 (v : BVec) : blochState v 1 0 = ((v 0 : ℂ) + Complex.I * (v 1 : ℂ)) / 2 := by
  simp [blochState, pauli0, pauli1, pauli2, Fin.sum_univ_three]
  ring



lemma herm_bs (v : BVec) : (blochState v)ᴴ = blochState v := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [Matrix.conjTranspose_apply, bs00, bs11, bs01, bs10, Complex.ext_iff]

lemma trace_bs (v : BVec) : (blochState v).trace = 1 := by
  simp [Matrix.trace, Fin.sum_univ_two, bs00, bs11]
  ring

lemma trsq_bs (v : BVec) : ((blochState v * blochState v).trace).re = (1 + ∑ α, v α ^ 2) / 2 := by
  simp [Matrix.trace, Matrix.mul_apply, Fin.sum_univ_two, Fin.sum_univ_three, bs00, bs11, bs01, bs10]
  ring_nf

end CoherenceTracking.Dephasing

open CoherenceTracking.Dephasing

theorem solution :
    (∀ ρ : Qmat, IsQubitState ρ →
        blochState (blochVec ρ) = ρ ∧ coherence ρ = 4 * Complex.normSq (ρ 0 1)) ∧
    (∀ v : BVec, blochVec (blochState v) = v) ∧
    (∀ v : BVec, IsQubitState (blochState v) ↔ ∑ α, v α ^ 2 ≤ 1) := by
  refine ⟨?_, ?_, ?_⟩
  · rintro ρ ⟨hH, hT, -⟩
    have h00 := congrFun (congrFun hH 0) 0
    have h11 := congrFun (congrFun hH 1) 1
    have h01 := congrFun (congrFun hH 0) 1
    have h10 := congrFun (congrFun hH 1) 0
    simp only [Matrix.conjTranspose_apply] at h00 h11 h01 h10
    have ht : ρ 0 0 + ρ 1 1 = 1 := by
      simpa [Matrix.trace, Fin.sum_univ_two] using hT
    rw [Complex.ext_iff] at h00 h11 h01 h10 ht
    simp at h00 h11 h01 h10 ht
    have key : blochState (blochVec ρ) = ρ := by
      ext i j
      fin_cases i <;> fin_cases j <;>
        simp [bs00, bs11, bs01, bs10, bv0, bv1, bv2, Complex.ext_iff] <;> constructor <;> nlinarith
    refine ⟨key, ?_⟩
    simp only [coherence, bv0, bv1, Complex.normSq_apply, Complex.add_re]
    rw [h10.1, ← h01.2]
    rw [show (ρ 1 0).im = -(ρ 0 1).im from by linarith [h10.2]]
    ring
  · intro v
    funext α
    fin_cases α
    · simp [bv0, bs01, bs10]
    · simp [bv1, bs01, bs10]; ring
    · simp [bv2, bs00, bs11]; ring
  · intro v
    refine ⟨fun h => ?_, fun h => ⟨herm_bs v, trace_bs v, ?_⟩⟩
    · have := h.2.2
      rw [trsq_bs] at this
      linarith
    · rw [trsq_bs]; linarith

