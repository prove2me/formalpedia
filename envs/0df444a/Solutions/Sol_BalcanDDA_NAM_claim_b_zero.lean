-- Prove2me | solution 1 for BalcanDDA.NAM.claim_b_zero
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-04T12:38:58.929986+00:00
-- url     : https://prove2.me/submissions/bf6b8e72-45e1-440e-bdd0-4a40f1a0c735

import Mathlib
import Definitions.Def_BalcanDDA_NAM_Model
import Definitions.Def_BalcanDDA_NAM_Construction

set_option autoImplicit false

open BalcanDDA.NAM in
theorem fe8ddb82_param_hi (n : ℕ) (b : Fin (n / 2) → Bool) (ℓ : Fin (n / 2))
    (hb : b ℓ = false) (h : n / 2 + (ℓ : ℕ) < n) :
    paramOf n b ⟨n / 2 + (ℓ : ℕ), h⟩ = 1 := by
  have hℓ := ℓ.isLt
  unfold paramOf
  have h1 : ¬ (n / 2 + (ℓ : ℕ) < n / 2) := by omega
  have h2 : n / 2 + (ℓ : ℕ) < n / 2 + n / 2 := by omega
  rw [dif_neg h1, dif_pos h2]
  have h3 : (⟨n / 2 + (ℓ : ℕ) - n / 2, by omega⟩ : Fin (n / 2)) = ℓ := by
    ext; simp
  rw [h3, hb]
  simp

open BalcanDDA.NAM in
theorem fe8ddb82_param_lo (n : ℕ) (b : Fin (n / 2) → Bool) (ℓ : Fin (n / 2))
    (hb : b ℓ = false) (i : Fin n) (hi : (i : ℕ) = ℓ) :
    paramOf n b i = 0 := by
  have hℓ := ℓ.isLt
  unfold paramOf
  have hi' : (i : ℕ) < n / 2 := by omega
  rw [dif_pos hi']
  have h3 : (⟨i, hi'⟩ : Fin (n / 2)) = ℓ := by ext; simp [hi]
  rw [h3, hb]
  simp

open BalcanDDA.NAM in
theorem fe8ddb82_wsum (n m : ℕ) (ε : ℝ) (b : Fin (n / 2) → Bool) (ℓ : Fin (n / 2))
    (hb : b ℓ = false) (j : Fin m) :
    ∑ i, paramOf n b i * profile n m ε ℓ i j = if (j : ℕ) = 1 then ε else 0 := by
  have hℓ := ℓ.isLt
  have hlt : n / 2 + (ℓ : ℕ) < n := by omega
  rw [Finset.sum_eq_single (⟨n / 2 + (ℓ : ℕ), hlt⟩ : Fin n)]
  · rw [fe8ddb82_param_hi n b ℓ hb hlt, one_mul]
    unfold profile
    have h4 : ¬ (n / 2 + (ℓ : ℕ) = (ℓ : ℕ)) := by omega
    simp only [Fin.val_mk, h4, false_and, if_false, true_and]
  · intro i _ hi
    unfold profile
    by_cases h5 : (i : ℕ) = (ℓ : ℕ) ∧ (j : ℕ) = 0
    · rw [if_pos h5, fe8ddb82_param_lo n b ℓ hb i h5.1]; ring
    · rw [if_neg h5]
      have h6 : ¬ ((i : ℕ) = n / 2 + (ℓ : ℕ) ∧ (j : ℕ) = 1) := by
        intro h; exact hi (Fin.ext h.1)
      rw [if_neg h6]; ring
  · intro h; exact absurd (Finset.mem_univ _) h

open BalcanDDA.NAM in
theorem solution (n m : ℕ) (hm : 2 ≤ m) (ε : ℝ) (hε0 : 0 < ε) (hε1 : ε < 1 / 2)
    (ψ : (Fin n → ℝ) → (Fin n → Fin m → ℝ) → Fin m) (hψ : IsArgmaxSelector ψ)
    (b : Fin (n / 2) → Bool) (ℓ : Fin (n / 2)) (hb : b ℓ = false) :
    welfare ψ (paramOf n b) (profile n m ε ℓ) = ε := by
  have key := hψ (paramOf n b) (profile n m ε ℓ) ⟨1, by omega⟩
  rw [fe8ddb82_wsum n m ε b ℓ hb, fe8ddb82_wsum n m ε b ℓ hb] at key
  unfold welfare
  generalize ψ (paramOf n b) (profile n m ε ℓ) = j at key ⊢
  have hj : (j : ℕ) = 1 := by
    by_contra h
    rw [if_neg h] at key
    simp at key
    linarith
  have hℓ := ℓ.isLt
  have hlt : n / 2 + (ℓ : ℕ) < n := by omega
  rw [Finset.sum_eq_single (⟨n / 2 + (ℓ : ℕ), hlt⟩ : Fin n)]
  · unfold profile
    simp [hj]
  · intro i _ hi
    unfold profile
    have h5 : ¬ ((i : ℕ) = (ℓ : ℕ) ∧ (j : ℕ) = 0) := by omega
    have h6 : ¬ ((i : ℕ) = n / 2 + (ℓ : ℕ) ∧ (j : ℕ) = 1) := by
      intro h; exact hi (Fin.ext h.1)
    rw [if_neg h5, if_neg h6]
  · intro h; exact absurd (Finset.mem_univ _) h
