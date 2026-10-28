-- Prove2me | solution 1 for CommonAgencyVCG.Algorithmic.claim_1
-- status  : ACCEPTED   (prove)
-- author  : @shivm
-- created : 2026-10-26T14:05:11.42305+00:00
-- url     : https://prove2.me/submissions/a4f32d36-812c-41eb-90db-b6be9cc7d917

import Mathlib
import Definitions.Def_CommonAgencyVCG_Algorithmic_Setting
import Definitions.Def_CommonAgencyVCG_Algorithmic_Alg1

namespace Aux_CAVCG_claim1

open CommonAgencyVCG.Algorithmic

variable {n : ℕ} {A O : Type} [Fintype A] [Nonempty A] [Fintype O]

lemma exists_aStar (S : Setting n A O) (b : Fin n → O → ℝ) : ∃ a, IsAStar S b a := by
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

lemma aStar_spec (S : Setting n A O) (b : Fin n → O → ℝ) : IsAStar S b (aStar S b) := by
  unfold aStar
  exact Classical.epsilon_spec (exists_aStar S b)

lemma E_zero (S : Setting n A O) (a : A) : E S a 0 = 0 := by
  unfold E; simp

lemma Wel_update (S : Setting n A O) (a : A) (b : Fin n → O → ℝ) (ℓ : Fin n) (v : O → ℝ) :
    Wel S a (Function.update b ℓ v) = Wel S a (Function.update b ℓ 0) + E S a v := by
  classical
  have key : ∀ w : O → ℝ, ∑ k, E S a (Function.update b ℓ w k) =
      E S a w + ∑ k ∈ Finset.univ.erase ℓ, E S a (b k) := by
    intro w
    rw [← Finset.add_sum_erase _ _ (Finset.mem_univ ℓ), Function.update_self]
    congr 1
    apply Finset.sum_congr rfl
    intro k hk
    rw [Function.update_of_ne (Finset.ne_of_mem_erase hk)]
  unfold Wel
  rw [key, key, E_zero]
  ring

lemma choice_unique (S : Setting n A O) (hS : S.Standing) (t : Contract n O)
    (b : Fin n → O → ℝ) (a a2 : A) (h1 : agentChoice S t b a) (h2 : agentChoice S t b a2) :
    a = a2 := by
  have hu1 := h1.1 a2
  have hu2 := h2.1 a
  have heq : agentUtil S t b a2 = agentUtil S t b a := le_antisymm hu1 hu2
  have c1 := h1.2 a2 heq
  have c2 := h2.2 a heq.symm
  apply hS.2.1
  rcases c1 with c1 | ⟨c1, c1'⟩ <;> rcases c2 with c2 | ⟨c2, c2'⟩
  · linarith
  · linarith
  · linarith
  · linarith

lemma inDom_update (S : Setting n A O) (b : Fin n → O → ℝ) (hb : InDom S b) (ℓ : Fin n)
    (v : O → ℝ) (hv : v ∈ S.V ℓ) : InDom S (Function.update b ℓ v) := by
  intro k
  by_cases hk : k = ℓ
  · subst hk; rw [Function.update_self]; exact hv
  · rw [Function.update_of_ne hk]; exact hb k

end Aux_CAVCG_claim1

open CommonAgencyVCG.Algorithmic Aux_CAVCG_claim1 in
theorem solution {n : ℕ} {A O : Type} [Fintype A] [Nonempty A] [Fintype O]
    (S : Setting n A O) (hS : S.Standing) (t : Contract n O) (ht : IsIIVCG S t) :
    IsIR S t ↔ ∀ ℓ b, InDom S b → E S (aStar S b) (t b ℓ) ≤ mBound S ℓ b := by
  classical
  obtain ⟨hchoice, h, hloc, hrep⟩ := ht
  constructor
  · intro hIR ℓ b hb
    unfold mBound
    rw [hrep b hb ℓ]
    have hne : Nonempty (S.V ℓ) := (hS.2.2.2.2.1 ℓ).to_subtype
    have : h ℓ b ≤ hAlg S ℓ b := by
      unfold hAlg
      apply le_ciInf
      rintro ⟨v, hv⟩
      set b' := Function.update b ℓ v with hb'
      have hb'D : InDom S b' := inDom_update S b hb ℓ v hv
      have hir := hIR ℓ b v hb hv (aStar S b') (hchoice b' hb'D)
      rw [← hb', hrep b' hb'D ℓ] at hir
      have hh : h ℓ b' = h ℓ b := hloc ℓ b' b (fun k hk => by
        rw [hb', Function.update_of_ne hk])
      have hu : Function.update b' ℓ 0 = Function.update b ℓ 0 := by
        rw [hb', Function.update_idem]
      rw [hh, hu] at hir
      have hw := Wel_update S (aStar S b') b ℓ v
      rw [← hb'] at hw
      show h ℓ b ≤ Wel S (aStar S b') b'
      linarith
    linarith
  · intro hR ℓ b v hb hv a ha
    set b' := Function.update b ℓ v with hb'
    have hb'D : InDom S b' := inDom_update S b hb ℓ v hv
    have haeq : a = aStar S b' := choice_unique S hS t b' a _ ha (hchoice b' hb'D)
    subst haeq
    have h1 := hR ℓ b' hb'D
    unfold mBound at h1
    have hbdd : BddBelow (Set.range fun v' : S.V ℓ =>
        Wel S (aStar S (Function.update b' ℓ v')) (Function.update b' ℓ v')) := by
      obtain ⟨a0⟩ := (inferInstance : Nonempty A)
      refine ⟨-S.psi a0, ?_⟩
      rintro x ⟨⟨v', hv'⟩, rfl⟩
      have hD := inDom_update S b' hb'D ℓ v' hv'
      have hmax := (aStar_spec S (Function.update b' ℓ v')).1 a0
      have hpos : 0 ≤ ∑ k, E S a0 (Function.update b' ℓ v' k) := by
        apply Finset.sum_nonneg
        intro k _
        unfold E
        apply Finset.sum_nonneg
        intro o _
        exact mul_nonneg (hS.2.2.1 a0 o) (hS.2.2.2.2.2.1 k _ (hD k) o)
      unfold Wel at hmax
      dsimp only
      unfold Wel
      linarith
    have h2 : hAlg S ℓ b' ≤ Wel S (aStar S b') b' := by
      unfold hAlg
      have := ciInf_le hbdd ⟨v, hv⟩
      simp only [hb', Function.update_idem] at this ⊢
      exact this
    have hw := Wel_update S (aStar S b') b ℓ v
    have hu : Function.update b' ℓ 0 = Function.update b ℓ 0 := by
      rw [hb', Function.update_idem]
    rw [hu] at h1
    rw [← hb'] at hw
    linarith
