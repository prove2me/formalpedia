-- Prove2me | solution 1 for Diaz.failure_rational_multiple_rigid
-- status  : ACCEPTED   (prove)
-- author  : @carlok
-- created : 2026-09-08T11:01:35.935984+00:00
-- url     : https://prove2.me/submissions/ebe064ae-a248-48a8-a299-1971ae7d1ce6

import Mathlib
import Theorems.Thm_DiazModulus_hermite_lindemann_holds

open ComplexConjugate

private theorem polar2_isAlgebraic_ratCast (q : ℚ) : IsAlgebraic ℚ ((q : ℂ)) := by
  have h := isAlgebraic_algebraMap (R := ℚ) (A := ℂ) q
  rwa [show (algebraMap ℚ ℂ) q = ((q : ℂ)) from rfl] at h

theorem solution {t₁ t₂ : ℝ} (ht₁ : t₁ ≠ 0)
    (e₁ : IsAlgebraic ℚ ((Real.exp t₁ : ℝ) : ℂ))
    (h₁ : IsAlgebraic ℚ ((t₁ ^ 2 + Real.pi ^ 2 : ℝ) : ℂ))
    (h₂ : IsAlgebraic ℚ ((t₂ ^ 2 + Real.pi ^ 2 : ℝ) : ℂ))
    (r : ℚ) (hr : t₂ = (r : ℝ) * t₁) : r = 1 ∨ r = -1 := by
  by_contra hcon
  rw [not_or] at hcon
  obtain ⟨hr1, hr2⟩ := hcon
  have hrsq : (1 - r ^ 2 : ℚ) ≠ 0 := by
    intro h
    have : (r - 1) * (r + 1) = 0 := by linarith [h]
    rcases mul_eq_zero.mp this with h' | h'
    · exact hr1 (by linarith)
    · exact hr2 (by linarith)
  have hdiff : IsAlgebraic ℚ ((((1 - r ^ 2 : ℚ) : ℝ) * t₁ ^ 2 : ℝ) : ℂ) := by
    have hrw : ((((1 - r ^ 2 : ℚ) : ℝ) * t₁ ^ 2 : ℝ) : ℂ)
        = ((t₁ ^ 2 + Real.pi ^ 2 : ℝ) : ℂ) - ((t₂ ^ 2 + Real.pi ^ 2 : ℝ) : ℂ) := by
      rw [← Complex.ofReal_sub]
      congr 1
      rw [hr]
      push_cast
      ring
    rw [hrw]
    exact h₁.sub h₂
  have hsq : IsAlgebraic ℚ ((t₁ ^ 2 : ℝ) : ℂ) := by
    have hrw : ((t₁ ^ 2 : ℝ) : ℂ)
        = ((((1 - r ^ 2 : ℚ)⁻¹ : ℚ)) : ℂ) * ((((1 - r ^ 2 : ℚ) : ℝ) * t₁ ^ 2 : ℝ) : ℂ) := by
      rw [Complex.ofReal_mul, ← mul_assoc, ← Complex.ofReal_ratCast, ← Complex.ofReal_mul]
      rw [show (((1 - r ^ 2 : ℚ)⁻¹ : ℚ) : ℝ) * (((1 - r ^ 2 : ℚ) : ℝ)) = 1 by
        rw [← Rat.cast_mul, inv_mul_cancel₀ hrsq, Rat.cast_one]]
      rw [Complex.ofReal_one, one_mul]
    rw [hrw]
    exact IsAlgebraic.mul (polar2_isAlgebraic_ratCast _) hdiff
  have ht₁alg : IsAlgebraic ℚ (((t₁ : ℝ)) : ℂ) := by
    refine IsAlgebraic.of_pow (n := 2) (by norm_num) ?_
    rwa [← Complex.ofReal_pow]
  have ht₁ne : ((t₁ : ℝ) : ℂ) ≠ 0 := by
    simpa using ht₁
  have := DiazModulus.hermite_lindemann_holds _ ht₁ne ht₁alg
  rw [← Complex.ofReal_exp] at this
  exact this e₁
