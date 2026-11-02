-- Prove2me | solution 1 for CommonAgencyVCG.Algorithmic.lemma_1
-- status  : ACCEPTED   (prove)
-- author  : @tianyipeng
-- created : 2026-11-01T07:39:59.20759+00:00
-- url     : https://prove2.me/submissions/0adab6dc-2ef4-4c5b-80f7-f83e12a9db24

import Mathlib
import Definitions.Def_CommonAgencyVCG_Algorithmic_Setting
import Definitions.Def_CommonAgencyVCG_Algorithmic_Alg1

namespace Aux_CAVCG_lemma1

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

omit [Nonempty A] in
lemma E_zero (S : Setting n A O) (a : A) : E S a 0 = 0 := by
  unfold E; simp

omit [Nonempty A] in
lemma E_sum (S : Setting n A O) (a : A) (b : Fin n → O → ℝ) :
    E S a (∑ ℓ, b ℓ) = ∑ ℓ, E S a (b ℓ) := by
  unfold E
  simp only [Finset.sum_apply, Finset.mul_sum]
  exact Finset.sum_comm

omit [Nonempty A] in
lemma E_const_add (S : Setting n A O) (hS : S.Standing) (a : A) (c : ℝ) (w : O → ℝ) :
    E S a (fun o => c + w o) = c + E S a w := by
  unfold E
  have h1 : ∑ o, S.F a o * (c + w o) = (∑ o, S.F a o) * c + ∑ o, S.F a o * w o := by
    rw [Finset.sum_mul, ← Finset.sum_add_distrib]
    apply Finset.sum_congr rfl
    intro o _
    ring
  rw [h1, hS.2.2.2.1 a, one_mul]

omit [Nonempty A] in
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

end Aux_CAVCG_lemma1

open CommonAgencyVCG.Algorithmic Aux_CAVCG_lemma1 in
theorem solution {n : ℕ} {A O : Type} [Fintype A] [Nonempty A] [Fintype O]
    (S : Setting n A O) (hS : S.Standing) (t : Contract n O) :
    IsIIVCG S t ↔
      ∃ h : Fin n → (Fin n → O → ℝ) → ℝ,
        (∀ ℓ b b', (∀ k, k ≠ ℓ → b k = b' k) → h ℓ b = h ℓ b') ∧
          ∀ b, InDom S b → ∃ w : Fin n → O → ℝ, (∀ ℓ o, 0 ≤ w ℓ o) ∧
            (∑ ℓ, w ℓ) ∈ implSet S (aStar S b) ∧
              ∀ ℓ o, t b ℓ o = h ℓ b - Wel S (aStar S b) (Function.update b ℓ (w ℓ)) + w ℓ o := by
  classical
  constructor
  · rintro ⟨hchoice, h, hloc, hrep⟩
    refine ⟨h, hloc, fun b hb => ?_⟩
    -- shift each payment by a constant making it non-negative
    let s : Fin n → ℝ := fun ℓ => ∑ o', |t b ℓ o'|
    let w : Fin n → O → ℝ := fun ℓ o => s ℓ + t b ℓ o
    have hwE : ∀ a ℓ, E S a (w ℓ) = s ℓ + E S a (t b ℓ) := fun a ℓ =>
      E_const_add S hS a (s ℓ) (t b ℓ)
    refine ⟨w, fun ℓ o => ?_, ⟨fun o => ?_, fun a' => ?_⟩, fun ℓ o => ?_⟩
    · have h1 : |t b ℓ o| ≤ s ℓ :=
        Finset.single_le_sum (f := fun o' => |t b ℓ o'|) (fun _ _ => abs_nonneg _)
          (Finset.mem_univ o)
      have h2 := neg_abs_le (t b ℓ o)
      show 0 ≤ s ℓ + t b ℓ o
      linarith
    · rw [Finset.sum_apply]
      exact Finset.sum_nonneg fun ℓ _ => by
        have h1 : |t b ℓ o| ≤ s ℓ :=
          Finset.single_le_sum (f := fun o' => |t b ℓ o'|) (fun _ _ => abs_nonneg _)
            (Finset.mem_univ o)
        have h2 := neg_abs_le (t b ℓ o)
        show 0 ≤ s ℓ + t b ℓ o
        linarith
    · rw [E_sum, E_sum]
      simp only [hwE, Finset.sum_add_distrib]
      have := (hchoice b hb).1 a'
      unfold agentUtil at this
      linarith
    · rw [Wel_update, hwE, hrep b hb ℓ]
      show t b ℓ o = h ℓ b - (Wel S (aStar S b) (Function.update b ℓ 0) +
        (s ℓ + (h ℓ b - Wel S (aStar S b) (Function.update b ℓ 0)))) + (s ℓ + t b ℓ o)
      ring
  · rintro ⟨h, hloc, hrep⟩
    have hEt : ∀ b, InDom S b → ∀ w : Fin n → O → ℝ,
        (∀ ℓ o, t b ℓ o = h ℓ b - Wel S (aStar S b) (Function.update b ℓ (w ℓ)) + w ℓ o) →
        ∀ ℓ a', E S a' (t b ℓ) =
          (h ℓ b - Wel S (aStar S b) (Function.update b ℓ (w ℓ))) + E S a' (w ℓ) := by
      intro b _ w hw ℓ a'
      have : t b ℓ = fun o => (h ℓ b - Wel S (aStar S b) (Function.update b ℓ (w ℓ))) + w ℓ o :=
        funext (hw ℓ)
      rw [this, E_const_add S hS]
    refine ⟨fun b hb => ?_, h, hloc, fun b hb ℓ => ?_⟩
    · obtain ⟨w, _, hwL, hw⟩ := hrep b hb
      have hutil : ∀ a', agentUtil S t b a' =
          (∑ ℓ, (h ℓ b - Wel S (aStar S b) (Function.update b ℓ (w ℓ)))) +
            E S a' (∑ ℓ, w ℓ) - S.psi a' := by
        intro a'
        unfold agentUtil
        rw [E_sum]
        simp only [hEt b hb w hw _ a', Finset.sum_add_distrib]
      have hspec := aStar_spec S b
      refine ⟨fun a' => ?_, fun a' _ => ?_⟩
      · rw [hutil, hutil]
        have := hwL.2 a'
        linarith
      · rcases lt_or_eq_of_le (hspec.1 a') with h' | h'
        · exact Or.inl h'
        · exact Or.inr ⟨h', hspec.2 a' h'⟩
    · obtain ⟨w, _, _, hw⟩ := hrep b hb
      rw [hEt b hb w hw ℓ, Wel_update]
      ring
