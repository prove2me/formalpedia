-- Prove2me | solution 1 for CommonAgencyVCG.Algorithmic.observation_3
-- status  : ACCEPTED   (prove)
-- author  : @shivm
-- created : 2026-10-26T15:37:34.49728+00:00
-- url     : https://prove2.me/submissions/4256789c-416c-4b37-a54e-135594399551

import Mathlib
import Definitions.Def_CommonAgencyVCG_Algorithmic_Setting
import Definitions.Def_CommonAgencyVCG_Algorithmic_Alg1

namespace Aux_CAVCG_obs3

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

end Aux_CAVCG_obs3

open CommonAgencyVCG.Algorithmic Aux_CAVCG_obs3 in
theorem solution {n : ℕ} {A O : Type} [Fintype A] [Nonempty A] [Fintype O]
    (S : Setting n A O) (hS : S.Standing) (b : Fin n → O → ℝ) (hb : InDom S b)
    (hk : kCost S (aStar S b) ≤ ∑ ℓ, mBound S ℓ b) :
    (∃ x : Fin n → ℝ, (∀ ℓ, 0 ≤ x ℓ ∧ x ℓ * kCost S (aStar S b) ≤ mBound S ℓ b) ∧ ∑ ℓ, x ℓ = 1) ∧
      ∀ x : Fin n → ℝ,
        (((∑ ℓ, x ℓ ≤ 1) ∧ ∀ ℓ, 0 ≤ x ℓ ∧ x ℓ * kCost S (aStar S b) ≤ mBound S ℓ b) ∧
            ∀ y : Fin n → ℝ, ((∑ ℓ, y ℓ ≤ 1) ∧
                ∀ ℓ, 0 ≤ y ℓ ∧ y ℓ * kCost S (aStar S b) ≤ mBound S ℓ b) →
              ∑ ℓ, y ℓ ≤ ∑ ℓ, x ℓ) ↔
          ((∀ ℓ, 0 ≤ x ℓ ∧ x ℓ * kCost S (aStar S b) ≤ mBound S ℓ b) ∧ ∑ ℓ, x ℓ = 1) := by
  classical
  set k := kCost S (aStar S b) with hkdef
  -- E is nonnegative on nonnegative vectors
  have hEnn : ∀ a (w : O → ℝ), (∀ o, 0 ≤ w o) → 0 ≤ E S a w := by
    intro a w hw
    unfold E
    exact Finset.sum_nonneg (fun o _ => mul_nonneg (hS.2.2.1 a o) (hw o))
  have hk0 : 0 ≤ k := by
    rw [hkdef]; unfold kCost
    exact Real.iInf_nonneg (fun w => hEnn _ _ w.2.1)
  have hm0 : ∀ ℓ, 0 ≤ mBound S ℓ b := by
    intro ℓ
    unfold mBound hAlg
    have hne : Nonempty (S.V ℓ) := (hS.2.2.2.2.1 ℓ).to_subtype
    have : Wel S (aStar S b) (Function.update b ℓ 0) ≤
        ⨅ v : S.V ℓ, Wel S (aStar S (Function.update b ℓ v)) (Function.update b ℓ v) := by
      apply le_ciInf
      rintro ⟨v, hv⟩
      have h1 := (aStar_spec S (Function.update b ℓ v)).1 (aStar S b)
      have h2 := Wel_update S (aStar S b) b ℓ v
      have h3 := hEnn (aStar S b) v (hS.2.2.2.2.2.1 ℓ v hv)
      linarith
    linarith
  have hn : 0 < n := hS.1
  have hex : ∃ x : Fin n → ℝ, (∀ ℓ, 0 ≤ x ℓ ∧ x ℓ * k ≤ mBound S ℓ b) ∧ ∑ ℓ, x ℓ = 1 := by
    rcases eq_or_lt_of_le hk0 with hk0' | hkpos
    · refine ⟨fun _ => 1 / (n : ℝ), fun ℓ => ⟨by positivity, ?_⟩, ?_⟩
      · rw [← hk0', mul_zero]; exact hm0 ℓ
      · rw [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
        have : (n : ℝ) ≠ 0 := by exact_mod_cast hn.ne'
        field_simp
    · set M := ∑ ℓ, mBound S ℓ b with hM
      have hMpos : 0 < M := lt_of_lt_of_le hkpos hk
      refine ⟨fun ℓ => mBound S ℓ b / M, fun ℓ => ⟨div_nonneg (hm0 ℓ) hMpos.le, ?_⟩, ?_⟩
      · rw [div_mul_eq_mul_div, div_le_iff₀ hMpos]
        exact mul_le_mul_of_nonneg_left hk (hm0 ℓ)
      · rw [← Finset.sum_div, ← hM, div_self hMpos.ne']
  refine ⟨hex, fun x => ⟨?_, ?_⟩⟩
  · rintro ⟨⟨hle, hfeas⟩, hopt⟩
    obtain ⟨x0, hx0, hsum0⟩ := hex
    have := hopt x0 ⟨hsum0.le, hx0⟩
    exact ⟨hfeas, le_antisymm hle (hsum0 ▸ this)⟩
  · rintro ⟨hfeas, hsum⟩
    refine ⟨⟨hsum.le, hfeas⟩, fun y hy => ?_⟩
    rw [hsum]; exact hy.1
