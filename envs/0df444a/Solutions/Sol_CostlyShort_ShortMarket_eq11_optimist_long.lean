-- Prove2me | solution 1 for CostlyShort.ShortMarket.eq11_optimist_long
-- status  : ACCEPTED   (prove)
-- author  : @vebis
-- created : 2026-10-21T06:22:12.473164+00:00
-- url     : https://prove2.me/submissions/fedcc354-0e9f-4440-b87e-4ab425ecca84

import Mathlib
import Definitions.Def_CostlyShort_ShortMarket_Setting

set_option autoImplicit false

open CostlyShort.ShortMarket

theorem solution {σ₁ σ₂ S₁ Wo Wp θ₁o θ₁p θ₂o θ₂p γ φ : ℝ} {po pp : ℝ × ℝ}
    (hσ₁ : 0 < σ₁) (hσ₂ : 0 < σ₂) (hS₁ : 0 < S₁) (hWo : 0 < Wo) (hWp : 0 < Wp)
    (hΔ : θ₁p ≤ θ₁o)
    (heq : IsShortMarketEquilibrium σ₁ σ₂ S₁ Wo Wp θ₁o θ₁p θ₂o θ₂p γ φ po pp) :
    0 < θ₂o := by
  by_contra hneg
  push_neg at hneg
  have hθp : θ₂p ≤ 0 := by
    have h1 := heq.eq7_o
    have h2 := heq.eq7_p
    linarith
  -- an agent with a nonpositive net Sharpe ratio never holds a positive position in asset 1
  have key : ∀ (θ₁ θ₂ : ℝ) (p : ℝ × ℝ), θ₂ = θ₁ + γ → θ₂ ≤ 0 →
      IsOptimalFractions σ₁ σ₂ (φ * σ₁) (γ * σ₁) θ₁ θ₂ p → p.1 ≤ 0 := by
    intro θ₁ θ₂ p h7 hθ hopt
    by_contra hp
    push_neg at hp
    have hp2 : 0 ≤ p.2 := hopt.1
    have h0 := hopt.2 (0, 0) le_rfl
    have h1 : mvObjective σ₁ σ₂ (φ * σ₁) (γ * σ₁) θ₁ θ₂ (0, 0) = 0 := by
      simp [mvObjective, lendingFlow]
    have h2 : mvObjective σ₁ σ₂ (φ * σ₁) (γ * σ₁) θ₁ θ₂ p =
        (p.1 * σ₁ + p.2 * σ₂) * θ₂ - (p.1 * σ₁ + p.2 * σ₂) ^ 2 / 2 := by
      unfold mvObjective lendingFlow
      rw [max_eq_left hp.le, max_eq_right (by linarith : -p.1 ≤ 0), h7]
      ring
    have hs : 0 < p.1 * σ₁ + p.2 * σ₂ := by
      nlinarith [mul_pos hp hσ₁, mul_nonneg hp2 hσ₂.le]
    rw [h1, h2] at h0
    nlinarith [mul_pos hs hs, mul_nonpos_of_nonneg_of_nonpos hs.le hθ]
  have h1 := key θ₁o θ₂o po heq.eq7_o hneg heq.opt_o
  have h2 := key θ₁p θ₂p pp heq.eq7_p hθp heq.opt_p
  have hc := heq.clear_asset1
  nlinarith [mul_nonneg hWo.le (neg_nonneg.2 h1), mul_nonneg hWp.le (neg_nonneg.2 h2)]
