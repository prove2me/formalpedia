-- Prove2me | solution 1 for BalcanDDA.NAM.claim_b_one
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-04T12:52:55.633091+00:00
-- url     : https://prove2.me/submissions/90cd7505-575d-4f69-a927-ed8ba2b8a95a

import Mathlib
import Definitions.Def_BalcanDDA_NAM_Model
import Definitions.Def_BalcanDDA_NAM_Construction

set_option autoImplicit false

open BalcanDDA.NAM in
lemma balcan38816788_sum_fin_ite (n k : ℕ) (hk : k < n) (c : ℝ) :
    ∑ i : Fin n, (if (i : ℕ) = k then c else 0) = c := by
  have h : ∀ i : Fin n, ((i : ℕ) = k) ↔ i = ⟨k, hk⟩ := fun i => by simp [Fin.ext_iff]
  simp_rw [h]
  simp

open BalcanDDA.NAM in
lemma balcan38816788_term (n m : ℕ) (ε : ℝ) (b : Fin (n / 2) → Bool) (ℓ : Fin (n / 2))
    (hb : b ℓ = true) (i : Fin n) (j : Fin m) :
    paramOf n b i * profile n m ε ℓ i j = if (i : ℕ) = ℓ ∧ (j : ℕ) = 0 then 1 else 0 := by
  have hℓ := ℓ.isLt
  unfold paramOf profile
  by_cases h1 : (i : ℕ) = ℓ ∧ (j : ℕ) = 0
  · have hi : (i : ℕ) < n / 2 := by omega
    have e : (⟨i, hi⟩ : Fin (n / 2)) = ℓ := Fin.ext h1.1
    rw [if_pos h1, if_pos h1, dif_pos hi, e, hb]
    simp
  · by_cases h2 : (i : ℕ) = n / 2 + ℓ ∧ (j : ℕ) = 1
    · have hi : ¬ (i : ℕ) < n / 2 := by omega
      have hi' : (i : ℕ) < n / 2 + n / 2 := by omega
      have e : (⟨(i : ℕ) - n / 2, by omega⟩ : Fin (n / 2)) = ℓ := Fin.ext (by simp; omega)
      rw [if_neg h1, if_neg h1, if_pos h2, dif_neg hi, dif_pos hi', e, hb]
      simp
    · rw [if_neg h1, if_neg h1, if_neg h2]
      simp

open BalcanDDA.NAM in
theorem solution (n m : ℕ) (hm : 2 ≤ m) (ε : ℝ) (hε0 : 0 < ε) (hε1 : ε < 1 / 2)
    (ψ : (Fin n → ℝ) → (Fin n → Fin m → ℝ) → Fin m) (hψ : IsArgmaxSelector ψ)
    (b : Fin (n / 2) → Bool) (ℓ : Fin (n / 2)) (hb : b ℓ = true) :
    welfare ψ (paramOf n b) (profile n m ε ℓ) = 1 := by
  have hℓ := ℓ.isLt
  have hℓn : (ℓ : ℕ) < n := by omega
  have hw : ∀ j : Fin m, ∑ i, paramOf n b i * profile n m ε ℓ i j
      = if (j : ℕ) = 0 then 1 else 0 := by
    intro j
    simp_rw [balcan38816788_term n m ε b ℓ hb]
    by_cases hj : (j : ℕ) = 0
    · simp only [hj, and_true, if_true]
      exact balcan38816788_sum_fin_ite n ℓ hℓn 1
    · simp [hj]
  have h0 := hψ (paramOf n b) (profile n m ε ℓ) ⟨0, by omega⟩
  rw [hw, hw] at h0
  have hψ0 : ((ψ (paramOf n b) (profile n m ε ℓ) : Fin m) : ℕ) = 0 := by
    by_contra hne
    rw [if_neg hne] at h0
    have h10 : ¬ ((1 : ℝ) ≤ 0) := by norm_num
    first
      | exact h10 h0
      | (simp only [Fin.val_zero, if_true] at h0; exact h10 h0)
      | (norm_num at h0)
  unfold welfare
  generalize ψ (paramOf n b) (profile n m ε ℓ) = x at hψ0 ⊢
  have hv : ∀ i : Fin n, profile n m ε ℓ i x = if (i : ℕ) = ℓ then 1 else 0 := by
    intro i
    unfold profile
    by_cases hi : (i : ℕ) = ℓ
    · rw [if_pos ⟨hi, hψ0⟩, if_pos hi]
    · rw [if_neg (fun h => hi h.1), if_neg hi, if_neg (fun h => by omega)]
  simp_rw [hv]
  exact balcan38816788_sum_fin_ite n ℓ hℓn 1
