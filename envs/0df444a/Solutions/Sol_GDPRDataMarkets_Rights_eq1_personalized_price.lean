-- Prove2me | solution 1 for GDPRDataMarkets.Rights.eq1_personalized_price
-- status  : ACCEPTED   (prove)
-- author  : @vebis
-- created : 2026-10-21T17:41:34.902321+00:00
-- url     : https://prove2.me/submissions/8e056686-a9ea-4281-be5d-3cc21d696da9

import Mathlib
import Definitions.Def_GDPRDataMarkets_Rights_Model

set_option autoImplicit false
open GDPRDataMarkets.Rights

theorem solution (P : Params) (hS : P.Standing) (v q : ℝ)
    (hv : v ∈ Set.Icc (0 : ℝ) 1) (hq : q ≤ v) :
    (P.kH * v - P.c ≤ 2 * (P.kL * v - P.c) ∧ 0 ≤ P.kH * v - P.c →
        ∀ ρ : ℝ, R P v q ρ ≤ R P v q (P.kL * v + q - P.c)) ∧
    (max (2 * (P.kL * v - P.c)) 0 ≤ P.kH * v - P.c →
        ∀ ρ : ℝ, R P v q ρ ≤ R P v q (P.kH * v + q - P.c)) ∧
    (max (P.kH * v - P.c) (2 * (P.kL * v - P.c)) ≤ 0 →
        ∀ ρ : ℝ, P.kH * v + q - P.c < ρ → ∀ ρ' : ℝ, R P v q ρ' ≤ R P v q ρ) := by
  obtain ⟨hL, hLH, -⟩ := hS
  have hkv : P.kL * v ≤ P.kH * v := mul_le_mul_of_nonneg_right hLH.le hv.1
  have hR : ∀ ρ : ℝ, R P v q ρ =
      ((if ρ ≤ P.kL * v + q - P.c then ρ else q) +
        (if ρ ≤ P.kH * v + q - P.c then ρ else q)) / 2 := by
    intro ρ
    unfold R rev2opt
    rw [max_eq_left (by linarith : (0:ℝ) ≤ v - q)]
    have e1 : (v - q ≤ (1 + P.kL) * v - ρ - P.c) ↔ ρ ≤ P.kL * v + q - P.c := by
      constructor <;> intro h <;> linarith
    have e2 : (v - q ≤ (1 + P.kH) * v - ρ - P.c) ↔ ρ ≤ P.kH * v + q - P.c := by
      constructor <;> intro h <;> linarith
    simp only [e1, e2, hq, if_true]
  refine ⟨?_, ?_, ?_⟩
  · rintro ⟨h1, h2⟩ ρ
    rw [hR, hR]
    split_ifs <;> linarith
  · intro h ρ
    have h1 := le_trans (le_max_left _ _) h
    have h2 := le_trans (le_max_right _ _) h
    rw [hR, hR]
    split_ifs <;> linarith
  · intro h ρ hρ ρ'
    have h1 := le_trans (le_max_left _ _) h
    have h2 := le_trans (le_max_right _ _) h
    rw [hR, hR]
    split_ifs <;> linarith
