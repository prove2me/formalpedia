-- Prove2me | solution 1 for BaconThesis.Supercoherence.commute_codeHamiltonian
-- status  : ACCEPTED   (prove)
-- author  : @shivm
-- created : 2026-11-07T15:30:36.525604+00:00
-- url     : https://prove2.me/submissions/48b06034-01c0-4f36-91a9-11a6dc78332e

import Mathlib
import Definitions.Def_QMaxCutSDP_Rounding_Pauli
import Definitions.Def_BaconThesis_Supercoherence_S1
import Definitions.Def_BaconThesis_Supercoherence_S2
import Definitions.Def_BaconThesis_Supercoherence_X2bar
import Definitions.Def_BaconThesis_Supercoherence_Z2bar
import Definitions.Def_BaconThesis_Supercoherence_codeHamiltonian

open QMaxCutSDP.Rounding Matrix

namespace Aux_BaconThesis_Supercoherence_commute_codeHamiltonian

lemma mul_string' {n : ℕ} (s t : Fin n → Fin 4) :
    pauliString s * pauliString t =
      fun x y => ∏ i, (pauli (s i) * pauli (t i)) (x i) (y i) := by
  ext x y
  simp only [Matrix.mul_apply, pauliString]
  calc ∑ z : BitString n, (∏ i, pauli (s i) (x i) (z i)) * ∏ i, pauli (t i) (z i) (y i)
      = ∑ z : BitString n, ∏ i, (pauli (s i) (x i) (z i) * pauli (t i) (z i) (y i)) := by
        refine Finset.sum_congr rfl fun z _ => ?_
        rw [Finset.prod_mul_distrib]
    _ = ∏ i, ∑ c : Fin 2, pauli (s i) (x i) c * pauli (t i) c (y i) :=
        (Fintype.prod_sum (fun i (c : Fin 2) => pauli (s i) (x i) c * pauli (t i) c (y i))).symm
    _ = ∏ i, (pauli (s i) * pauli (t i)) (x i) (y i) := by
        refine Finset.prod_congr rfl fun i _ => ?_
        rw [Matrix.mul_apply]

lemma comm_string {n : ℕ} (s t : Fin n → Fin 4) (ε : Fin n → ℂ)
    (h : ∀ i, pauli (s i) * pauli (t i) = ε i • (pauli (t i) * pauli (s i)))
    (hε : ∏ i, ε i = 1) : Commute (pauliString s) (pauliString t) := by
  show pauliString s * pauliString t = pauliString t * pauliString s
  rw [mul_string', mul_string']
  funext x y
  simp only [h, Matrix.smul_apply, smul_eq_mul]
  rw [Finset.prod_mul_distrib, hε, one_mul]

lemma p0 : pauli 0 = 1 := by
  ext a b; fin_cases a <;> fin_cases b <;> simp [pauli]

lemma c_eq (a : Fin 4) : pauli a * pauli a = (1 : ℂ) • (pauli a * pauli a) := by
  rw [one_smul]
lemma c_l0 (a : Fin 4) : pauli 0 * pauli a = (1 : ℂ) • (pauli a * pauli 0) := by
  rw [p0, one_mul, mul_one, one_smul]
lemma c_r0 (a : Fin 4) : pauli a * pauli 0 = (1 : ℂ) • (pauli 0 * pauli a) := by
  rw [p0, one_mul, mul_one, one_smul]
lemma c13 : pauli 1 * pauli 3 = (-1 : ℂ) • (pauli 3 * pauli 1) := by
  ext a b; fin_cases a <;> fin_cases b <;> simp [pauli, Matrix.mul_apply, Fin.sum_univ_two]
lemma c31 : pauli 3 * pauli 1 = (-1 : ℂ) • (pauli 1 * pauli 3) := by
  ext a b; fin_cases a <;> fin_cases b <;> simp [pauli, Matrix.mul_apply, Fin.sum_univ_two]

end Aux_BaconThesis_Supercoherence_commute_codeHamiltonian

open BaconThesis.Supercoherence Aux_BaconThesis_Supercoherence_commute_codeHamiltonian in
theorem solution :
    Commute S1 codeHamiltonian ∧ Commute S2 codeHamiltonian ∧ Commute Z2bar codeHamiltonian ∧
      Commute X2bar codeHamiltonian := by
  unfold S1 S2 Z2bar X2bar codeHamiltonian
  refine ⟨?_, ?_, ?_, ?_⟩
  · refine ((Commute.add_right ?_ ?_).add_right ?_).add_right ?_
    · refine comm_string _ _ ![1, 1, 1, 1] ?_ ?_
      · intro i
        fin_cases i
        exacts [c_eq _, c_eq _, c_r0 _, c_r0 _]
      · simp [Fin.prod_univ_four]
    · refine comm_string _ _ ![1, 1, 1, 1] ?_ ?_
      · intro i
        fin_cases i
        exacts [c_r0 _, c_r0 _, c_eq _, c_eq _]
      · simp [Fin.prod_univ_four]
    · refine comm_string _ _ ![1, -1, -1, 1] ?_ ?_
      · intro i
        fin_cases i
        exacts [c_r0 _, c13, c13, c_r0 _]
      · simp [Fin.prod_univ_four]
    · refine comm_string _ _ ![-1, 1, 1, -1] ?_ ?_
      · intro i
        fin_cases i
        exacts [c13, c_r0 _, c_r0 _, c13]
      · simp [Fin.prod_univ_four]
  · refine ((Commute.add_right ?_ ?_).add_right ?_).add_right ?_
    · refine comm_string _ _ ![-1, -1, 1, 1] ?_ ?_
      · intro i
        fin_cases i
        exacts [c31, c31, c_r0 _, c_r0 _]
      · simp [Fin.prod_univ_four]
    · refine comm_string _ _ ![1, 1, -1, -1] ?_ ?_
      · intro i
        fin_cases i
        exacts [c_r0 _, c_r0 _, c31, c31]
      · simp [Fin.prod_univ_four]
    · refine comm_string _ _ ![1, 1, 1, 1] ?_ ?_
      · intro i
        fin_cases i
        exacts [c_r0 _, c_eq _, c_eq _, c_r0 _]
      · simp [Fin.prod_univ_four]
    · refine comm_string _ _ ![1, 1, 1, 1] ?_ ?_
      · intro i
        fin_cases i
        exacts [c_eq _, c_r0 _, c_r0 _, c_eq _]
      · simp [Fin.prod_univ_four]
  · refine ((Commute.add_right ?_ ?_).add_right ?_).add_right ?_
    · refine comm_string _ _ ![-1, -1, 1, 1] ?_ ?_
      · intro i
        fin_cases i
        exacts [c31, c31, c_eq _, c_eq _]
      · simp [Fin.prod_univ_four]
    · refine comm_string _ _ ![1, 1, 1, 1] ?_ ?_
      · intro i
        fin_cases i
        exacts [c_r0 _, c_r0 _, c_l0 _, c_l0 _]
      · simp [Fin.prod_univ_four]
    · refine comm_string _ _ ![1, 1, 1, 1] ?_ ?_
      · intro i
        fin_cases i
        exacts [c_r0 _, c_eq _, c_l0 _, c_eq _]
      · simp [Fin.prod_univ_four]
    · refine comm_string _ _ ![1, 1, 1, 1] ?_ ?_
      · intro i
        fin_cases i
        exacts [c_eq _, c_r0 _, c_eq _, c_l0 _]
      · simp [Fin.prod_univ_four]
  · refine ((Commute.add_right ?_ ?_).add_right ?_).add_right ?_
    · refine comm_string _ _ ![1, 1, 1, 1] ?_ ?_
      · intro i
        fin_cases i
        exacts [c_l0 _, c_eq _, c_r0 _, c_eq _]
      · simp [Fin.prod_univ_four]
    · refine comm_string _ _ ![1, 1, 1, 1] ?_ ?_
      · intro i
        fin_cases i
        exacts [c_eq _, c_r0 _, c_eq _, c_l0 _]
      · simp [Fin.prod_univ_four]
    · refine comm_string _ _ ![1, -1, -1, 1] ?_ ?_
      · intro i
        fin_cases i
        exacts [c_eq _, c13, c13, c_eq _]
      · simp [Fin.prod_univ_four]
    · refine comm_string _ _ ![1, 1, 1, 1] ?_ ?_
      · intro i
        fin_cases i
        exacts [c_l0 _, c_r0 _, c_r0 _, c_l0 _]
      · simp [Fin.prod_univ_four]
