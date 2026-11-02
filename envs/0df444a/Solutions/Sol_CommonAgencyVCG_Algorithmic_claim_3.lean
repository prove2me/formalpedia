-- Prove2me | solution 1 for CommonAgencyVCG.Algorithmic.claim_3
-- status  : ACCEPTED   (prove)
-- author  : @tianyipeng
-- created : 2026-11-01T07:37:52.218197+00:00
-- url     : https://prove2.me/submissions/5de0fd1c-6431-4b28-8216-f5b293ba0191

import Mathlib
import Definitions.Def_CommonAgencyVCG_Algorithmic_Setting
import Definitions.Def_CommonAgencyVCG_Algorithmic_Alg1
import Theorems.Thm_CommonAgencyVCG_Algorithmic_proposition_4
import Theorems.Thm_CommonAgencyVCG_Algorithmic_observation_3
import Theorems.Thm_CommonAgencyVCG_Algorithmic_claim_1

namespace Aux_CAVCG_claim3

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
lemma E_smul (S : Setting n A O) (a : A) (x : ℝ) (w : O → ℝ) :
    E S a (x • w) = x * E S a w := by
  unfold E
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro o _
  simp only [Pi.smul_apply, smul_eq_mul]
  ring

omit [Nonempty A] in
lemma E_affine (S : Setting n A O) (hS : S.Standing) (a : A) (c d : ℝ) (w : O → ℝ) :
    E S a (fun o => c + d * w o) = c + d * E S a w := by
  unfold E
  have h1 : ∑ o, S.F a o * (c + d * w o) = (∑ o, S.F a o) * c + d * ∑ o, S.F a o * w o := by
    rw [Finset.sum_mul, Finset.mul_sum, ← Finset.sum_add_distrib]
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

/-- Part 2 of Claim 3: for admissible selections, ALG1 is IIVCG, LL and IR. -/
lemma alg1_good (S : Setting n A O) (hS : S.Standing)
    (wsel : (Fin n → O → ℝ) → O → ℝ) (xsel : (Fin n → O → ℝ) → Fin n → ℝ)
    (hv : ValidSel S wsel xsel) :
    IsIIVCG S (alg1 S wsel xsel) ∧ IsLL S (alg1 S wsel xsel) ∧ IsIR S (alg1 S wsel xsel) := by
  classical
  set t := alg1 S wsel xsel with ht
  -- the constant part of t^ℓ(b, ·)
  have hconst : ∀ b ℓ, t b ℓ = fun o =>
      (hAlg S ℓ b - Wel S (aStar S b) (Function.update b ℓ (xsel b ℓ • wsel b))) +
        xsel b ℓ * wsel b o := fun b ℓ => rfl
  have hEt : ∀ b ℓ a', E S a' (t b ℓ) =
      (hAlg S ℓ b - Wel S (aStar S b) (Function.update b ℓ (xsel b ℓ • wsel b))) +
        xsel b ℓ * E S a' (wsel b) := by
    intro b ℓ a'
    rw [hconst b ℓ, E_affine S hS]
  have hWelx : ∀ b ℓ, Wel S (aStar S b) (Function.update b ℓ (xsel b ℓ • wsel b)) =
      Wel S (aStar S b) (Function.update b ℓ 0) + xsel b ℓ * E S (aStar S b) (wsel b) := by
    intro b ℓ
    rw [Wel_update, E_smul]
  -- expected payment at a*(b)
  have hEstar : ∀ b ℓ, E S (aStar S b) (t b ℓ) =
      hAlg S ℓ b - Wel S (aStar S b) (Function.update b ℓ 0) := by
    intro b ℓ
    rw [hEt, hWelx]
    ring
  have hIIVCG : IsIIVCG S t := by
    refine ⟨?_, hAlg S, ?_, ?_⟩
    · intro b hb
      obtain ⟨hwimp, _, _, hxsum⟩ := hv b hb
      have hutil : ∀ a', agentUtil S t b a' =
          (∑ ℓ, (hAlg S ℓ b - Wel S (aStar S b) (Function.update b ℓ (xsel b ℓ • wsel b)))) +
            E S a' (wsel b) - S.psi a' := by
        intro a'
        unfold agentUtil
        simp only [hEt b _ a', Finset.sum_add_distrib, ← Finset.sum_mul, hxsum, one_mul]
      have hspec := aStar_spec S b
      refine ⟨fun a' => ?_, fun a' _ => ?_⟩
      · rw [hutil, hutil]
        have := hwimp.2 a'
        linarith
      · rcases lt_or_eq_of_le (hspec.1 a') with h | h
        · exact Or.inl h
        · exact Or.inr ⟨h, hspec.2 a' h⟩
    · intro ℓ b b' hbb
      unfold hAlg
      have : ∀ v : O → ℝ, Function.update b ℓ v = Function.update b' ℓ v := by
        intro v
        funext k
        by_cases hk : k = ℓ
        · subst hk; simp
        · rw [Function.update_of_ne hk, Function.update_of_ne hk]; exact hbb k hk
      simp only [this]
    · intro b _ ℓ
      exact hEstar b ℓ
  have hLL : IsLL S t := by
    intro b hb ℓ o
    obtain ⟨hwimp, hwk, hx, _⟩ := hv b hb
    rw [hconst b ℓ]
    dsimp only
    rw [hWelx, hwk]
    have h1 := (hx ℓ).2
    have h2 : 0 ≤ xsel b ℓ * wsel b o := mul_nonneg (hx ℓ).1 (hwimp.1 o)
    unfold mBound at h1
    linarith
  have hIR : IsIR S t := by
    rw [claim_1 S hS t hIIVCG]
    intro ℓ b _
    rw [hEstar]
    unfold mBound
    exact le_rfl
  exact ⟨hIIVCG, hLL, hIR⟩

end Aux_CAVCG_claim3

open CommonAgencyVCG.Algorithmic Aux_CAVCG_claim3 in
theorem solution {n : ℕ} {A O : Type} [Fintype A] [Nonempty A] [Fintype O]
    (S : Setting n A O) (hS : S.Standing)
    (hk : ∀ b, InDom S b → kCost S (aStar S b) ≤ ∑ ℓ, mBound S ℓ b) :
    (∃ (wsel : (Fin n → O → ℝ) → O → ℝ) (xsel : (Fin n → O → ℝ) → Fin n → ℝ),
      ValidSel S wsel xsel) ∧
    ∀ (wsel : (Fin n → O → ℝ) → O → ℝ) (xsel : (Fin n → O → ℝ) → Fin n → ℝ),
      ValidSel S wsel xsel →
        IsIIVCG S (alg1 S wsel xsel) ∧ IsLL S (alg1 S wsel xsel) ∧ IsIR S (alg1 S wsel xsel) := by
  classical
  refine ⟨?_, fun wsel xsel hv => alg1_good S hS wsel xsel hv⟩
  let wsel : (Fin n → O → ℝ) → O → ℝ := fun b =>
    if h : InDom S b then Classical.choose (proposition_4 S hS b h) else 0
  let xsel : (Fin n → O → ℝ) → Fin n → ℝ := fun b =>
    if h : InDom S b then Classical.choose (observation_3 S hS b h (hk b h)).1 else 0
  refine ⟨wsel, xsel, fun b hb => ?_⟩
  have hw := Classical.choose_spec (proposition_4 S hS b hb)
  have hx := Classical.choose_spec (observation_3 S hS b hb (hk b hb)).1
  have ew : wsel b = Classical.choose (proposition_4 S hS b hb) := by simp [wsel, hb]
  have ex : xsel b = Classical.choose (observation_3 S hS b hb (hk b hb)).1 := by
    simp [xsel, hb]
  rw [ew, ex]
  exact ⟨hw.1, hw.2, hx.1, hx.2⟩
