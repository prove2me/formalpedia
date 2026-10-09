-- Prove2me | solution 1 for BookProof.BookBrstYangMills.gaussDer_apply
-- status  : ACCEPTED   (prove)
-- author  : @leonardopedro
-- created : 2026-10-09T05:40:54.24675+00:00
-- url     : https://prove2.me/submissions/6d02da8c-4837-4b5a-ac7d-6c70efc4851a

-- Generated from ChapterBookBrstYangMills.lean — solution of BookProof.BookBrstYangMills.gaussDer_apply
import Mathlib
import Definitions.Def_ChapterBookBrstYangMills
open BookProof.BookBrstYangMills




open MvPolynomial BookProof.BRSTNilpotent BookProof.QuantumGravityBrstCharge

noncomputable section

variable {N : ℕ} (G : GaugeAlgebra N)

set_option maxHeartbeats 1000000 in
theorem solution (c : Fin N) (p : FieldPoly N) :
    gaussDer G c p = ∑ i : Fin 4 × Fin N, gaussVec G c i * pderiv i p := by

  classical
  induction p using MvPolynomial.induction_on with
  | C a =>
      rw [show (C a : FieldPoly N) = algebraMap ℂ (FieldPoly N) a from rfl,
        Derivation.map_algebraMap]
      simp
  | add p q hp hq =>
      rw [map_add, hp, hq, ← Finset.sum_add_distrib]
      exact Finset.sum_congr rfl fun i _ => by rw [map_add, mul_add]
  | mul_X p i hp =>
      rw [Derivation.leibniz, hp, gaussDer_X]
      have hstep : ∀ j : Fin 4 × Fin N,
          gaussVec G c j * pderiv j (p * X i)
            = gaussVec G c j * pderiv j p * X i + (if j = i then gaussVec G c j * p else 0) := by
        intro j
        rw [Derivation.leibniz, MvPolynomial.pderiv_X]
        by_cases h : j = i
        · subst h
          simp [mul_add, mul_comm, mul_left_comm]
          ring
        · simp [h, mul_comm, mul_left_comm]
      rw [Finset.sum_congr rfl fun j _ => hstep j, Finset.sum_add_distrib,
        Finset.sum_ite_eq' Finset.univ i (fun j => gaussVec G c j * p)]
      simp only [Finset.mem_univ, if_pos, smul_eq_mul, Finset.mul_sum]
      rw [add_comm]
      congr 1
      · exact Finset.sum_congr rfl fun x _ => by ring
      · ring
