-- Prove2me | solution 1 for BaconThesis.Supercoherence.single_qubit_anticommute
-- status  : ACCEPTED   (prove)
-- author  : @shivm
-- created : 2026-11-07T15:26:41.412545+00:00
-- url     : https://prove2.me/submissions/920c7a4c-5912-4e90-aaef-c5338438d480

import Mathlib
import Definitions.Def_QMaxCutSDP_Rounding_Pauli
import Definitions.Def_BaconThesis_Supercoherence_S1
import Definitions.Def_BaconThesis_Supercoherence_S2

open QMaxCutSDP.Rounding Matrix

namespace Aux_BaconSQA

theorem mul_ps {n : ℕ} (s t : Fin n → Fin 4) (x y : BitString n) :
    (pauliString s * pauliString t) x y = ∏ i, (pauli (s i) * pauli (t i)) (x i) (y i) := by
  rw [Matrix.mul_apply]
  simp only [pauliString, Matrix.mul_apply]
  rw [Fintype.prod_sum]
  simp only [← Finset.prod_mul_distrib]

theorem p0 : pauli 0 = 1 := by
  unfold pauli
  rw [if_pos rfl]
  exact Matrix.one_fin_two.symm

theorem anti {n : ℕ} (i : Fin n) (a b : Fin 4)
    (hab : pauli a * pauli b = -(pauli b * pauli a)) (B : Fin n → Fin 4) (hB : ∀ j, B j = b) :
    pauliAt a i * pauliString B = -(pauliString B * pauliAt a i) := by
  unfold pauliAt
  ext x y
  rw [Matrix.neg_apply, mul_ps, mul_ps]
  have key : ∀ j, (pauli (if j = i then a else 0) * pauli (B j)) (x j) (y j) =
      (if j = i then -1 else 1) * (pauli (B j) * pauli (if j = i then a else 0)) (x j) (y j) := by
    intro j
    rw [hB j]
    by_cases h : j = i
    · simp only [h, if_true, hab, Matrix.neg_apply]
      ring
    · simp only [h, if_false, p0, Matrix.one_mul, Matrix.mul_one, one_mul]
  rw [Finset.prod_congr rfl (fun j _ => key j), Finset.prod_mul_distrib, Finset.prod_ite_eq']
  simp

end Aux_BaconSQA

open BaconThesis.Supercoherence in
theorem solution (i : Fin 4) (a : Fin 4) (ha : a ≠ 0) :
    pauliAt a i * BaconThesis.Supercoherence.S1 = -(BaconThesis.Supercoherence.S1 * pauliAt a i) ∨
      pauliAt a i * BaconThesis.Supercoherence.S2 =
        -(BaconThesis.Supercoherence.S2 * pauliAt a i) := by
  have hX : ∀ c : Fin 4, c = 2 ∨ c = 3 → pauli c * pauli 1 = -(pauli 1 * pauli c) := by
    rintro c (rfl | rfl) <;> ext p q <;> fin_cases p <;> fin_cases q <;>
      simp [pauli, Matrix.mul_apply, Fin.sum_univ_two]
  have hZ : ∀ c : Fin 4, c = 1 ∨ c = 2 → pauli c * pauli 3 = -(pauli 3 * pauli c) := by
    rintro c (rfl | rfl) <;> ext p q <;> fin_cases p <;> fin_cases q <;>
      simp [pauli, Matrix.mul_apply, Fin.sum_univ_two]
  have hB1 : ∀ j, (![1, 1, 1, 1] : Fin 4 → Fin 4) j = 1 := by intro j; fin_cases j <;> rfl
  have hB3 : ∀ j, (![3, 3, 3, 3] : Fin 4 → Fin 4) j = 3 := by intro j; fin_cases j <;> rfl
  have h : a = 1 ∨ a = 2 ∨ a = 3 := by revert ha; revert a; decide
  rcases h with rfl | rfl | rfl
  · right
    unfold BaconThesis.Supercoherence.S2
    exact Aux_BaconSQA.anti i 1 3 (hZ 1 (Or.inl rfl)) _ hB3
  · left
    unfold BaconThesis.Supercoherence.S1
    exact Aux_BaconSQA.anti i 2 1 (hX 2 (Or.inl rfl)) _ hB1
  · left
    unfold BaconThesis.Supercoherence.S1
    exact Aux_BaconSQA.anti i 3 1 (hX 3 (Or.inr rfl)) _ hB1
