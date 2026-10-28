-- Prove2me | solution 1 for CommonAgencyVCG.Algorithmic.implSet_aStar_nonempty
-- status  : ACCEPTED   (prove)
-- author  : @shivm
-- created : 2026-10-26T14:01:14.314493+00:00
-- url     : https://prove2.me/submissions/ec2c5c29-4c96-4cb3-b7df-e52b8e7ddba0

import Mathlib
import Definitions.Def_CommonAgencyVCG_Algorithmic_Setting
import Definitions.Def_CommonAgencyVCG_Algorithmic_Alg1

namespace Aux_CAVCG_implSet

open CommonAgencyVCG.Algorithmic

lemma exists_aStar {n : ℕ} {A O : Type} [Fintype A] [Nonempty A] [Fintype O]
    (S : Setting n A O) (b : Fin n → O → ℝ) : ∃ a, IsAStar S b a := by
  classical
  obtain ⟨a0, _, ha0⟩ := Finset.exists_max_image Finset.univ (fun a => Wel S a b)
    Finset.univ_nonempty
  let M := Finset.univ.filter (fun a => ∀ a', Wel S a' b ≤ Wel S a b)
  have hM : M.Nonempty := ⟨a0, by simp [M]; exact fun a' => ha0 a' (Finset.mem_univ _)⟩
  obtain ⟨a, haM, ha⟩ := Finset.exists_max_image M S.psi hM
  have haM' : ∀ a', Wel S a' b ≤ Wel S a b := by simpa [M] using haM
  refine ⟨a, haM', fun a' heq => ha a' ?_⟩
  simp only [M, Finset.mem_filter, Finset.mem_univ, true_and]
  intro a''
  rw [heq]
  exact haM' a''

lemma E_sum {n : ℕ} {A O : Type} [Fintype A] [Fintype O]
    (S : Setting n A O) (a : A) (b : Fin n → O → ℝ) :
    E S a (∑ ℓ, b ℓ) = ∑ ℓ, E S a (b ℓ) := by
  unfold E
  simp only [Finset.sum_apply, Finset.mul_sum]
  exact Finset.sum_comm

end Aux_CAVCG_implSet

open CommonAgencyVCG.Algorithmic in
theorem solution {n : ℕ} {A O : Type} [Fintype A] [Nonempty A] [Fintype O]
    (S : Setting n A O) (hS : S.Standing) (b : Fin n → O → ℝ)
    (hb : InDom S b) : (implSet S (aStar S b)).Nonempty := by
  have hA : IsAStar S b (aStar S b) := by
    unfold aStar
    exact Classical.epsilon_spec (Aux_CAVCG_implSet.exists_aStar S b)
  refine ⟨∑ ℓ, b ℓ, ?_, ?_⟩
  · intro o
    rw [Finset.sum_apply]
    exact Finset.sum_nonneg (fun ℓ _ => hS.2.2.2.2.2.1 ℓ (b ℓ) (hb ℓ) o)
  · intro a'
    rw [Aux_CAVCG_implSet.E_sum, Aux_CAVCG_implSet.E_sum]
    exact hA.1 a'
