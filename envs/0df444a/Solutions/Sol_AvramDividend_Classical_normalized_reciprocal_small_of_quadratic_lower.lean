-- Prove2me | solution 1 for AvramDividend.Classical.normalized_reciprocal_small_of_quadratic_lower
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-10-23T11:05:43.862451+00:00
-- url     : https://prove2.me/submissions/5641e340-5bf6-493d-8370-c12f48a05524

import Mathlib.Analysis.SpecialFunctions.Exp
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring

-- A quadratic lower bound forces the normalised reciprocal to vanish at infinity.
set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

theorem solution
    (ψ : ℝ → ℝ) (q a β : ℝ) (ha : 0 < a)
    (hbound : ∀ θ : ℝ, β ≤ θ → a * θ ^ 2 ≤ ψ θ - q) :
    ∀ ε : ℝ, 0 < ε →
      ∃ θ : ℝ, β ≤ θ ∧ 0 < θ ∧ θ * (ψ θ - q)⁻¹ < ε := by
  intro ε hε
  have hp : 0 < a * ε := mul_pos ha hε
  let θ : ℝ := max β ((a * ε)⁻¹) + 1
  have hβ : β ≤ θ := by
    dsimp [θ]
    have h := le_max_left β ((a * ε)⁻¹)
    linarith
  have hinv : (a * ε)⁻¹ < θ := by
    dsimp [θ]
    have h := le_max_right β ((a * ε)⁻¹)
    linarith
  have hθ : 0 < θ := by
    have hinvpos : 0 < (a * ε)⁻¹ := inv_pos.mpr hp
    linarith
  have hbig : 1 < θ * (a * ε) := by
    have hmul := mul_lt_mul_of_pos_right hinv hp
    have hone : (a * ε)⁻¹ * (a * ε) = 1 := inv_mul_cancel₀ (ne_of_gt hp)
    linarith
  have hqbound := hbound θ hβ
  have hden : 0 < ψ θ - q := by
    nlinarith [sq_pos_of_pos hθ, mul_pos ha (sq_pos_of_pos hθ)]
  have hcore : θ < ε * (a * θ ^ 2) := by
    have hpr : 0 < θ * (θ * (a * ε) - 1) :=
      mul_pos hθ (by linarith [hbig])
    nlinarith [hpr]
  refine ⟨θ, hβ, hθ, ?_⟩
  rw [← div_eq_mul_inv]
  apply (div_lt_iff₀ hden).2
  have hmul := mul_le_mul_of_nonneg_left hqbound (le_of_lt hε)
  nlinarith [hcore, hmul]
