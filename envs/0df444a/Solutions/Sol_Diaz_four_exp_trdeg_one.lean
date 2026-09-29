-- Prove2me | solution 1 for Diaz.four_exp_trdeg_one
-- status  : ACCEPTED   (prove)
-- author  : @carlok
-- created : 2026-09-08T09:30:09.494547+00:00
-- url     : https://prove2.me/submissions/9add7c18-a92d-451e-a3d8-5d4dff1e7b6c

import Mathlib

open ComplexConjugate

theorem solution {K : Subfield ℂ}
    (hMaster : ∀ μ₁ ν₁ μ₂ ν₂ : ℂ,
      Complex.exp μ₁ ∈ K → Complex.exp ν₁ ∈ K → Complex.exp μ₂ ∈ K → Complex.exp ν₂ ∈ K →
      μ₁ ≠ 0 → ν₁ ≠ 0 → μ₂ ≠ 0 → ν₂ ≠ 0 →
      ∀ m : ℚ, m ≠ 0 → μ₂ * ν₂ = (m : ℂ) * (μ₁ * ν₁) →
      ((∃ c : ℚ, c ≠ 0 ∧ μ₂ = (c : ℂ) * μ₁) ∧ (∃ c : ℚ, c ≠ 0 ∧ ν₂ = (c : ℂ) * ν₁))
      ∨ ((∃ c : ℚ, c ≠ 0 ∧ μ₂ = (c : ℂ) * ν₁) ∧ (∃ c : ℚ, c ≠ 0 ∧ ν₂ = (c : ℂ) * μ₁))
      ∨ 2 ≤ Algebra.trdeg ℚ ↥(Algebra.adjoin ℚ ({μ₁, ν₁, μ₂, ν₂} : Set ℂ)))
    {l₁₁ l₁₂ l₂₁ l₂₂ : ℂ}
    (h₁₁ : Complex.exp l₁₁ ∈ K) (h₁₂ : Complex.exp l₁₂ ∈ K)
    (h₂₁ : Complex.exp l₂₁ ∈ K) (h₂₂ : Complex.exp l₂₂ ∈ K)
    (n₁₁ : l₁₁ ≠ 0) (n₁₂ : l₁₂ ≠ 0) (n₂₁ : l₂₁ ≠ 0) (n₂₂ : l₂₂ ≠ 0)
    (hdet : l₁₁ * l₂₂ = l₁₂ * l₂₁)
    (htd : Algebra.trdeg ℚ ↥(Algebra.adjoin ℚ ({l₁₁, l₁₂, l₂₁, l₂₂} : Set ℂ)) ≤ 1) :
    (∃ a b : ℚ, ¬(a = 0 ∧ b = 0) ∧
        (a : ℂ) * l₁₁ + (b : ℂ) * l₂₁ = 0 ∧ (a : ℂ) * l₁₂ + (b : ℂ) * l₂₂ = 0)
    ∨ (∃ a b : ℚ, ¬(a = 0 ∧ b = 0) ∧
        (a : ℂ) * l₁₁ + (b : ℂ) * l₁₂ = 0 ∧ (a : ℂ) * l₂₁ + (b : ℂ) * l₂₂ = 0) := by
  have hset : ({l₁₁, l₂₂, l₁₂, l₂₁} : Set ℂ) = ({l₁₁, l₁₂, l₂₁, l₂₂} : Set ℂ) := by
    ext x; simp; try tauto
  have hprod : l₁₂ * l₂₁ = ((1 : ℚ) : ℂ) * (l₁₁ * l₂₂) := by push_cast; linear_combination -hdet
  have hne : l₁₁ * l₂₂ ≠ 0 := mul_ne_zero n₁₁ n₂₂
  rcases hMaster l₁₁ l₂₂ l₁₂ l₂₁ h₁₁ h₂₂ h₁₂ h₂₁ n₁₁ n₂₂ n₁₂ n₂₁ 1 one_ne_zero hprod with
    ⟨⟨c, hc0, hc⟩, ⟨c', hc'0, hc'⟩⟩ | ⟨⟨c, hc0, hc⟩, ⟨c', hc'0, hc'⟩⟩ | htd2
  · -- (i) : l₁₂ = c l₁₁ and l₂₁ = c' l₂₂ ; the second column is c times the first
    have hcc : (c : ℂ) * (c' : ℂ) = 1 := by
      have h := hdet
      rw [hc, hc'] at h
      apply mul_left_cancel₀ hne
      linear_combination -h
    right
    refine ⟨c, -1, ?_, ?_, ?_⟩
    · rintro ⟨-, h⟩; exact absurd h (by norm_num)
    · push_cast; linear_combination -hc
    · push_cast; linear_combination (c : ℂ) * hc' + l₂₂ * hcc
  · -- (ii) : l₁₂ = c l₂₂ and l₂₁ = c' l₁₁ ; the second row is c' times the first
    have hcc : (c : ℂ) * (c' : ℂ) = 1 := by
      have h := hdet
      rw [hc, hc'] at h
      apply mul_left_cancel₀ hne
      linear_combination -h
    left
    refine ⟨c', -1, ?_, ?_, ?_⟩
    · rintro ⟨-, h⟩; exact absurd h (by norm_num)
    · push_cast; linear_combination -hc'
    · push_cast; linear_combination (c' : ℂ) * hc + l₂₂ * hcc
  · rw [hset] at htd2
    exact absurd (htd2.trans htd) (by norm_num)
