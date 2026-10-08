-- Prove2me | solution 1 for AvramDividend.Classical.positive_linear_exponent_eventually_above
-- status  : ACCEPTED   (prove)
-- author  : @miao
-- created : 2026-10-07T03:25:55.081265+00:00
-- url     : https://prove2.me/submissions/818bd7f7-dd05-4613-8aee-1bea49e258a6

import Mathlib

open Filter

theorem solution
    (ψ : ℝ → ℝ) (d q : ℝ) (hd : 0 < d)
    (hlim : Filter.Tendsto (fun θ : ℝ => ψ θ / θ)
      Filter.atTop (nhds d)) :
    ∃ θ₀ : ℝ, ∀ θ : ℝ, θ₀ ≤ θ → q < ψ θ := by
  have he : ∀ᶠ θ in atTop, d / 2 < ψ θ / θ :=
    hlim.eventually (eventually_gt_nhds (by linarith : d / 2 < d))
  obtain ⟨t, ht⟩ := eventually_atTop.1 he
  refine ⟨max t (max 1 (2 * (|q| + 1) / d)), ?_⟩
  intro θ hθ
  have hθp : 0 < θ := lt_of_lt_of_le (by norm_num : (0 : ℝ) < 1)
    ((le_max_left _ _).trans ((le_max_right _ _).trans hθ))
  have hl := ht θ ((le_max_left _ _).trans hθ)
  have hb : 2 * (|q| + 1) / d ≤ θ :=
    (le_max_right _ _).trans ((le_max_right _ _).trans hθ)
  have hp := (lt_div_iff₀ hθp).1 hl
  have hbd := (div_le_iff₀ hd).1 hb
  have hq := le_abs_self q
  nlinarith
#print axioms solution

