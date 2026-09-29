-- Prove2me | solution 1 for FirstOrderOpt.Nonconvex.generalized_projection_gradient_bound
-- status  : ACCEPTED   (disprove)
-- author  : @mrfancypants
-- created : 2026-09-27T23:21:11.121606+00:00
-- url     : https://prove2.me/submissions/467692d3-73ad-4bf1-8f80-7375abe5f62a

import Mathlib

open scoped RealInnerProductSpace

/-- Counterexample: nothing constrains the prox-function `V` (the book's Bregman distance of a
strongly convex `ω`). Take `E = ℝ`, `X = univ`, `h = 0`, `V = 0`, `g = 0`, `γ = 1`, `x = 0` and
`xPlus = 1`. Every point minimizes the zero objective, so `hmin` holds, but
`⟪g, P⟫ = 0 < 1 = ‖P‖² + (1/γ)(h xPlus - h x)` for `P = x - xPlus = -1`. -/
theorem solution : ¬ (∀ {E : Type} [NormedAddCommGroup E]
    [InnerProductSpace ℝ E] (X : Set E) (h : E → ℝ) (V : E → E → ℝ)
    (x xPlus g : E) (γ : ℝ) (hγ : 0 < γ) (hx : x ∈ X) (hxPlus : xPlus ∈ X)
    (hmin : ∀ u ∈ X, ⟪g, xPlus⟫ + (1 / γ) * V x xPlus + h xPlus ≤
      ⟪g, u⟫ + (1 / γ) * V x u + h u)
    (PXval : E) (hPX : PXval = (1 / γ) • (x - xPlus)),
    ⟪g, PXval⟫ ≥ ‖PXval‖ ^ 2 + (1 / γ) * (h xPlus - h x)) := by
  intro H
  have := H (E := ℝ) Set.univ (fun _ => 0) (fun _ _ => 0) 0 1 0 1 one_pos trivial trivial
    (fun u _ => by simp) (-1) (by norm_num)
  norm_num at this
