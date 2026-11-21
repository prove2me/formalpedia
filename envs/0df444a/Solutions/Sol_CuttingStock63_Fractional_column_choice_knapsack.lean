-- Prove2me | solution 1 for CuttingStock63.Fractional.column_choice_knapsack
-- status  : ACCEPTED   (prove)
-- author  : @ducloc
-- created : 2026-11-21T05:55:34.609107+00:00
-- url     : https://prove2.me/submissions/74598882-08f0-4821-995e-ab1454e19ea7

import Mathlib

theorem solution {m : ℕ} (L z₁ z₂ : ℝ) (l p₁ p₂ : Fin m → ℝ) :
    (∀ a : Fin m → ℕ,
      z₁ * (-1 + ∑ i, p₂ i * a i) - z₂ * (-(L - ∑ i, (a i : ℝ) * l i) + ∑ i, p₁ i * a i) =
        (L - ∑ i, (a i : ℝ) * l i) * z₂ - z₁ + ∑ i, (z₁ * p₂ i - z₂ * p₁ i) * a i) ∧
    (∀ a : Fin m → ℕ,
      z₁ * (-1 + ∑ i, p₂ i * a i) - z₂ * (-(L - ∑ i, (a i : ℝ) * l i) + ∑ i, p₁ i * a i) =
        (L * z₂ - z₁) - ∑ i, (-(z₁ * p₂ i - z₂ * p₁ i - z₂ * l i)) * a i) ∧
    (z₂ ≠ 0 → ∀ a : Fin m → ℕ, ∑ i, (a i : ℝ) * l i ≤ L →
      ((∀ a' : Fin m → ℕ, ∑ i, (a' i : ℝ) * l i ≤ L →
          (z₁ * (-1 + ∑ i, p₂ i * a i) - z₂ * (-(L - ∑ i, (a i : ℝ) * l i) + ∑ i, p₁ i * a i)) / z₂ ^ 2 ≤
            (z₁ * (-1 + ∑ i, p₂ i * a' i) - z₂ * (-(L - ∑ i, (a' i : ℝ) * l i) + ∑ i, p₁ i * a' i)) / z₂ ^ 2) ↔
        (∀ a' : Fin m → ℕ, ∑ i, (a' i : ℝ) * l i ≤ L →
          ∑ i, (-(z₁ * p₂ i - z₂ * p₁ i - z₂ * l i)) * a' i ≤
            ∑ i, (-(z₁ * p₂ i - z₂ * p₁ i - z₂ * l i)) * a i))) := by
  constructor
  · intro a
    have hSR : (∑ i, (z₁ * p₂ i - z₂ * p₁ i) * (a i : ℝ)) =
        z₁ * (∑ i, p₂ i * (a i : ℝ)) - z₂ * (∑ i, p₁ i * (a i : ℝ)) := by
      have e1 : ∀ i : Fin m, (z₁ * p₂ i - z₂ * p₁ i) * (a i : ℝ) =
          z₁ * (p₂ i * (a i : ℝ)) - z₂ * (p₁ i * (a i : ℝ)) := by
        intro i; ring
      simp only [e1, Finset.sum_sub_distrib, Finset.mul_sum]
    rw [hSR]
    ring
  constructor
  · intro a
    have hSR : (∑ i, (-(z₁ * p₂ i - z₂ * p₁ i - z₂ * l i)) * (a i : ℝ)) =
        -(z₁ * (∑ i, p₂ i * (a i : ℝ)) - z₂ * (∑ i, p₁ i * (a i : ℝ)) -
          z₂ * (∑ i, (a i : ℝ) * l i)) := by
      have e1 : ∀ i : Fin m, (-(z₁ * p₂ i - z₂ * p₁ i - z₂ * l i)) * (a i : ℝ) =
          -(z₁ * (p₂ i * (a i : ℝ)) - z₂ * (p₁ i * (a i : ℝ)) - z₂ * ((a i : ℝ) * l i)) := by
        intro i; ring
      simp only [e1, Finset.sum_neg_distrib, Finset.sum_sub_distrib, Finset.mul_sum]
    rw [hSR]
    ring
  · intro hz₂ a ha
    have hA : ∀ a' : Fin m → ℕ,
        z₁ * (-1 + ∑ i, p₂ i * a' i) - z₂ * (-(L - ∑ i, (a' i : ℝ) * l i) + ∑ i, p₁ i * a' i) =
          (L * z₂ - z₁) - ∑ i, (-(z₁ * p₂ i - z₂ * p₁ i - z₂ * l i)) * a' i := by
      intro a'
      have hSR : (∑ i, (-(z₁ * p₂ i - z₂ * p₁ i - z₂ * l i)) * (a' i : ℝ)) =
          -(z₁ * (∑ i, p₂ i * (a' i : ℝ)) - z₂ * (∑ i, p₁ i * (a' i : ℝ)) -
            z₂ * (∑ i, (a' i : ℝ) * l i)) := by
        have e1 : ∀ i : Fin m, (-(z₁ * p₂ i - z₂ * p₁ i - z₂ * l i)) * (a' i : ℝ) =
            -(z₁ * (p₂ i * (a' i : ℝ)) - z₂ * (p₁ i * (a' i : ℝ)) - z₂ * ((a' i : ℝ) * l i)) := by
          intro i; ring
        simp only [e1, Finset.sum_neg_distrib, Finset.sum_sub_distrib, Finset.mul_sum]
      rw [hSR]
      ring
    have hpos : 0 < z₂ ^ 2 := by
      have h := abs_pos.mpr hz₂
      nlinarith [sq_abs z₂]
    constructor
    · intro h a' ha'
      have h1 : ((L * z₂ - z₁) - ∑ i, (-(z₁ * p₂ i - z₂ * p₁ i - z₂ * l i)) * a i) / z₂ ^ 2 ≤
          ((L * z₂ - z₁) - ∑ i, (-(z₁ * p₂ i - z₂ * p₁ i - z₂ * l i)) * a' i) / z₂ ^ 2 := by
        rw [← hA a, ← hA a']
        exact h a' ha'
      rw [div_le_div_iff_of_pos_right hpos] at h1
      linarith
    · intro h a' ha'
      have h1 : ∑ i, (-(z₁ * p₂ i - z₂ * p₁ i - z₂ * l i)) * a' i ≤
          ∑ i, (-(z₁ * p₂ i - z₂ * p₁ i - z₂ * l i)) * a i := h a' ha'
      rw [div_le_div_iff_of_pos_right hpos]
      rw [hA a, hA a']
      linarith
