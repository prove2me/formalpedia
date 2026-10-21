-- Prove2me | solution 1 for AvramDividend.Classical.positive_esscher_shift_laplace_domain
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-10-20T06:47:01.072655+00:00
-- url     : https://prove2.me/submissions/2d524f84-9aaf-4b50-b558-ea7df9e311d5

import Mathlib.Data.Real.Basic
import Mathlib.Tactic.Linarith

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

/-- Eventual positivity of an exponent is preserved after any positive Esscher shift. -/
theorem solution
    (ψ : ℝ → ℝ) (q φ β : ℝ) (hφ : 0 < φ)
    (hpos : ∀ θ : ℝ, β ≤ θ → q < ψ θ) :
    ∃ b : ℝ, ∀ θ : ℝ, b < θ →
      0 ≤ θ + φ ∧ q < ψ (θ + φ) := by
  refine ⟨max 0 β, ?_⟩
  intro θ hθ
  have hzero : 0 ≤ θ := by
    have hh := le_max_left (0 : ℝ) β
    linarith
  have hβ : β ≤ θ + φ := by
    have hh := le_max_right (0 : ℝ) β
    linarith
  exact ⟨by linarith, hpos (θ + φ) hβ⟩
