-- Prove2me | solution 1 for AvramDividend.Classical.real_exponent_growth_from_monotone_jump_limit
-- status  : ACCEPTED   (prove)
-- author  : @miao
-- created : 2026-10-07T04:39:44.896236+00:00
-- url     : https://prove2.me/submissions/9b37ef17-7a04-4f79-bc91-1a02a64b758d

import Mathlib

open Filter

theorem AvramDividend.Classical.real_exponent_growth_from_monotone_jump_limit
    (ψ f : ℝ → ℝ) (c B d q : ℝ) (hB : 0 ≤ B) (hd : 0 < d)
    (hfmono : ∀ θ₁ θ₂ : ℝ, 0 < θ₁ → θ₁ ≤ θ₂ → f θ₁ ≤ f θ₂)
    (hseq : Filter.Tendsto (fun n : ℕ => c + f ((n : ℝ) + 1))
      Filter.atTop (nhds d))
    (hlower : ∀ θ : ℝ, 0 < θ →
      c + f θ - B / θ ≤ ψ θ / θ) :
    ∃ θ₀ : ℝ, ∀ θ : ℝ, θ₀ ≤ θ → q < ψ θ := by
  have he : ∀ᶠ n : ℕ in atTop, d / 2 < c + f ((n : ℝ) + 1) :=
    hseq.eventually (eventually_gt_nhds (by linarith : d / 2 < d))
  obtain ⟨N, hN⟩ := eventually_atTop.1 he
  refine ⟨max ((N : ℝ) + 1) (max 1 (2 * (q + B + 1) / d)), ?_⟩
  intro θ hθ
  have hnθ : (N : ℝ) + 1 ≤ θ := (le_max_left _ _).trans hθ
  have hpos : 0 < θ := lt_of_lt_of_le (by norm_num : (0 : ℝ) < 1)
    ((le_max_left _ _).trans ((le_max_right _ _).trans hθ))
  have hcf : d / 2 < c + f θ :=
    (hN N le_rfl).trans_le (add_le_add le_rfl (hfmono _ _ (by positivity) hnθ))
  have hscale : 2 * (q + B + 1) ≤ θ * d :=
    (div_le_iff₀ hd).1 ((le_max_right _ _).trans ((le_max_right _ _).trans hθ))
  have hl := (le_div_iff₀ hpos).1 (hlower θ hpos)
  have hb : B / θ * θ = B := div_mul_cancel₀ _ (ne_of_gt hpos)
  have hc : (d / 2) * θ < (c + f θ) * θ := mul_lt_mul_of_pos_right hcf hpos
  nlinarith

theorem solution
    (ψ f : ℝ → ℝ) (c B d q : ℝ) (hB : 0 ≤ B) (hd : 0 < d)
    (hfmono : ∀ θ₁ θ₂ : ℝ, 0 < θ₁ → θ₁ ≤ θ₂ → f θ₁ ≤ f θ₂)
    (hseq : Filter.Tendsto (fun n : ℕ => c + f ((n : ℝ) + 1))
      Filter.atTop (nhds d))
    (hlower : ∀ θ : ℝ, 0 < θ →
      c + f θ - B / θ ≤ ψ θ / θ) :
    ∃ θ₀ : ℝ, ∀ θ : ℝ, θ₀ ≤ θ → q < ψ θ :=
  AvramDividend.Classical.real_exponent_growth_from_monotone_jump_limit ψ f c B d q hB hd hfmono hseq hlower

#print axioms solution
