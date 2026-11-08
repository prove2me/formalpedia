-- Prove2me | solution 1 for BaconThesis.Supercoherence.eq_15_9
-- status  : ACCEPTED   (prove)
-- author  : @shivm
-- created : 2026-11-08T01:34:00.047429+00:00
-- url     : https://prove2.me/submissions/b8a75b21-9d4e-4557-891e-e6809eb23450

import Mathlib
import Definitions.Def_QMaxCutSDP_Rounding_Pauli
import Definitions.Def_BaconThesis_Supercoherence_S1
import Definitions.Def_BaconThesis_Supercoherence_S2
import Definitions.Def_BaconThesis_Supercoherence_X1bar
import Definitions.Def_BaconThesis_Supercoherence_Z1bar
import Definitions.Def_BaconThesis_Supercoherence_codeHamiltonian

open QMaxCutSDP.Rounding Matrix

namespace Aux_Bacon159

lemma sum_prod_swap {n : ℕ} (P Q : Fin n → Fin 2 → ℂ) :
    ∑ z : Fin n → Fin 2, ∏ i, (P i (z i) * Q i (z i)) = ∏ i, ∑ c : Fin 2, P i c * Q i c :=
  (Fintype.prod_sum (fun i c => P i c * Q i c)).symm

lemma mul_ps {n : ℕ} (s t u : Fin n → Fin 4) (h : ∀ i, pauli (s i) * pauli (t i) = pauli (u i)) :
    pauliString s * pauliString t = pauliString u := by
  ext x y
  rw [Matrix.mul_apply]
  simp only [pauliString]
  have h1 : ∀ z : Fin n → Fin 2,
      (∏ i, pauli (s i) (x i) (z i)) * (∏ i, pauli (t i) (z i) (y i)) =
        ∏ i, (pauli (s i) (x i) (z i) * pauli (t i) (z i) (y i)) :=
    fun z => Finset.prod_mul_distrib.symm
  rw [Finset.sum_congr rfl (fun z _ => h1 z),
    sum_prod_swap (fun i c => pauli (s i) (x i) c) (fun i c => pauli (t i) c (y i))]
  apply Finset.prod_congr rfl
  intro i _
  rw [← h i, Matrix.mul_apply]

lemma p11 : pauli 1 * pauli 1 = pauli 0 := by
  ext i j; fin_cases i <;> fin_cases j <;> simp [pauli, Matrix.mul_apply, Fin.sum_univ_two]
lemma p01 : pauli 0 * pauli 1 = pauli 1 := by
  ext i j; fin_cases i <;> fin_cases j <;> simp [pauli, Matrix.mul_apply, Fin.sum_univ_two]
lemma p33 : pauli 3 * pauli 3 = pauli 0 := by
  ext i j; fin_cases i <;> fin_cases j <;> simp [pauli, Matrix.mul_apply, Fin.sum_univ_two]
lemma p03 : pauli 0 * pauli 3 = pauli 3 := by
  ext i j; fin_cases i <;> fin_cases j <;> simp [pauli, Matrix.mul_apply, Fin.sum_univ_two]

end Aux_Bacon159

open BaconThesis.Supercoherence in
theorem solution (v : (Fin 4 → Fin 2) → ℂ) :
    (S1 *ᵥ v = v → S2 *ᵥ v = v → codeHamiltonian *ᵥ v = ((2 : ℂ) • (X1bar + Z1bar)) *ᵥ v) ∧
      (S1 *ᵥ v = v → S2 *ᵥ v = -v → codeHamiltonian *ᵥ v = ((2 : ℂ) • X1bar) *ᵥ v) ∧
      (S1 *ᵥ v = -v → S2 *ᵥ v = v → codeHamiltonian *ᵥ v = ((2 : ℂ) • Z1bar) *ᵥ v) ∧
      (S1 *ᵥ v = -v → S2 *ᵥ v = -v → codeHamiltonian *ᵥ v = 0) := by
  have hX : pauliString ![0, 0, 1, 1] = X1bar * S1 := by
    unfold X1bar S1
    refine (Aux_Bacon159.mul_ps _ _ _ ?_).symm
    intro i
    fin_cases i
    · exact Aux_Bacon159.p11
    · exact Aux_Bacon159.p11
    · exact Aux_Bacon159.p01
    · exact Aux_Bacon159.p01
  have hZ : pauliString ![3, 0, 0, 3] = Z1bar * S2 := by
    unfold Z1bar S2
    refine (Aux_Bacon159.mul_ps _ _ _ ?_).symm
    intro i
    fin_cases i
    · exact Aux_Bacon159.p03
    · exact Aux_Bacon159.p33
    · exact Aux_Bacon159.p33
    · exact Aux_Bacon159.p03
  have hH : codeHamiltonian *ᵥ v =
      X1bar *ᵥ v + X1bar *ᵥ (S1 *ᵥ v) + Z1bar *ᵥ v + Z1bar *ᵥ (S2 *ᵥ v) := by
    unfold codeHamiltonian
    rw [hX, hZ, Matrix.add_mulVec, Matrix.add_mulVec, Matrix.add_mulVec, ← Matrix.mulVec_mulVec,
      ← Matrix.mulVec_mulVec]
    rfl
  refine ⟨fun h1 h2 => ?_, fun h1 h2 => ?_, fun h1 h2 => ?_, fun h1 h2 => ?_⟩
  · rw [hH, h1, h2, Matrix.smul_mulVec, Matrix.add_mulVec, two_smul]; abel
  · rw [hH, h1, h2, Matrix.mulVec_neg, Matrix.smul_mulVec, two_smul]; abel
  · rw [hH, h1, h2, Matrix.mulVec_neg, Matrix.smul_mulVec, two_smul]; abel
  · rw [hH, h1, h2, Matrix.mulVec_neg, Matrix.mulVec_neg]; abel
