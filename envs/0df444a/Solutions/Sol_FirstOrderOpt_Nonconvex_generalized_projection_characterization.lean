-- Prove2me | solution 1 for FirstOrderOpt.Nonconvex.generalized_projection_characterization
-- status  : ACCEPTED   (disprove)
-- author  : @mrfancypants
-- created : 2026-09-27T23:21:11.811681+00:00
-- url     : https://prove2.me/submissions/0d67da47-822b-4035-adf8-2207a1f20081

import Mathlib

open scoped RealInnerProductSpace

/-- Counterexample: nothing constrains `V` (the book's Bregman distance, which vanishes on the
diagonal and satisfies the three-point identity). With `V ≡ 1`, `E = ℝ`, `X = univ`, `h = 0`,
`g = 0`, `γ = 1` and `x = xPlus = 0`, the minimality hypothesis reads `1 ≤ 1`, while the
conclusion at `u = 0` reads `1 ≤ 1 * (1 - 1) = 0`. -/
theorem solution : ¬ (∀ {E : Type} [NormedAddCommGroup E]
    [InnerProductSpace ℝ E] (X : Set E) (h : E → ℝ) (V : E → E → ℝ)
    (x xPlus g : E) (γ : ℝ) (hγ : 0 < γ) (hx : x ∈ X) (hxPlus : xPlus ∈ X)
    (hmin : ∀ u ∈ X, ⟪g, xPlus⟫ + (1 / γ) * V x xPlus + h xPlus ≤
      ⟪g, u⟫ + (1 / γ) * V x u + h u),
    ∀ u ∈ X, ⟪g, xPlus⟫ + h xPlus + (1 / γ) * V x xPlus ≤
      ⟪g, u⟫ + h u + (1 / γ) * (V x u - V xPlus u)) := by
  intro H
  have := H (E := ℝ) Set.univ (fun _ => 0) (fun _ _ => 1) 0 0 0 1 one_pos trivial trivial
    (fun u _ => by simp) 0 trivial
  norm_num at this
