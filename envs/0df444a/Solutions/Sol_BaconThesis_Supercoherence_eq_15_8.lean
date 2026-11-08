-- Prove2me | solution 1 for BaconThesis.Supercoherence.eq_15_8
-- status  : ACCEPTED   (prove)
-- author  : @shivm
-- created : 2026-11-07T14:43:57.956208+00:00
-- url     : https://prove2.me/submissions/238dc71d-4870-4c34-8d99-7d5f99d785a4

import Mathlib
import Definitions.Def_QMaxCutSDP_Rounding_Pauli
import Definitions.Def_BaconThesis_Supercoherence_S1
import Definitions.Def_BaconThesis_Supercoherence_S2
import Definitions.Def_BaconThesis_Supercoherence_X1bar
import Definitions.Def_BaconThesis_Supercoherence_Z1bar
import Definitions.Def_BaconThesis_Supercoherence_codeHamiltonian

open QMaxCutSDP.Rounding Matrix

namespace Aux_BaconThesis_Supercoherence_eq_15_8

lemma mul_string {n : ℕ} (s t u : Fin n → Fin 4)
    (h : ∀ i, pauli (s i) * pauli (t i) = pauli (u i)) :
    pauliString s * pauliString t = pauliString u := by
  ext x y
  simp only [Matrix.mul_apply, pauliString]
  calc ∑ z : BitString n, (∏ i, pauli (s i) (x i) (z i)) * ∏ i, pauli (t i) (z i) (y i)
      = ∑ z : BitString n, ∏ i, (pauli (s i) (x i) (z i) * pauli (t i) (z i) (y i)) := by
        refine Finset.sum_congr rfl fun z _ => ?_
        rw [Finset.prod_mul_distrib]
    _ = ∏ i, ∑ c : Fin 2, pauli (s i) (x i) c * pauli (t i) c (y i) :=
        (Fintype.prod_sum (fun i (c : Fin 2) => pauli (s i) (x i) c * pauli (t i) c (y i))).symm
    _ = ∏ i, pauli (u i) (x i) (y i) := by
        refine Finset.prod_congr rfl fun i _ => ?_
        rw [← h i, Matrix.mul_apply]

lemma p11 : pauli 1 * pauli 1 = pauli 0 := by
  ext a b; fin_cases a <;> fin_cases b <;> simp [pauli, Matrix.mul_apply, Fin.sum_univ_two]
lemma p01 : pauli 0 * pauli 1 = pauli 1 := by
  ext a b; fin_cases a <;> fin_cases b <;> simp [pauli, Matrix.mul_apply, Fin.sum_univ_two]
lemma p03 : pauli 0 * pauli 3 = pauli 3 := by
  ext a b; fin_cases a <;> fin_cases b <;> simp [pauli, Matrix.mul_apply, Fin.sum_univ_two]
lemma p33 : pauli 3 * pauli 3 = pauli 0 := by
  ext a b; fin_cases a <;> fin_cases b <;> simp [pauli, Matrix.mul_apply, Fin.sum_univ_two]

lemma hX : pauliString ![1, 1, 0, 0] * pauliString ![1, 1, 1, 1] = pauliString ![0, 0, 1, 1] := by
  apply mul_string
  intro i
  fin_cases i
  exacts [p11, p11, p01, p01]

lemma hZ : pauliString ![0, 3, 3, 0] * pauliString ![3, 3, 3, 3] = pauliString ![3, 0, 0, 3] := by
  apply mul_string
  intro i
  fin_cases i
  exacts [p03, p33, p33, p03]

end Aux_BaconThesis_Supercoherence_eq_15_8

open BaconThesis.Supercoherence in
theorem solution :
    codeHamiltonian = X1bar + X1bar * S1 + Z1bar + Z1bar * S2 ∧
      codeHamiltonian = X1bar * (1 + S1) + Z1bar * (1 + S2) := by
  have h1 : codeHamiltonian = X1bar + X1bar * S1 + Z1bar + Z1bar * S2 := by
    unfold codeHamiltonian X1bar S1 Z1bar S2
    rw [Aux_BaconThesis_Supercoherence_eq_15_8.hX, Aux_BaconThesis_Supercoherence_eq_15_8.hZ] <;> abel
  refine ⟨h1, ?_⟩
  rw [h1, mul_add, mul_add, mul_one, mul_one] <;> abel
