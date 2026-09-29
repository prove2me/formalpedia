-- Prove2me | solution 1 for FirstOrderOpt.Deterministic.mirror_iterate_three_point
-- status  : ACCEPTED   (disprove)
-- author  : @mrfancypants
-- created : 2026-09-28T22:45:43.096895+00:00
-- url     : https://prove2.me/submissions/4a99cd5c-66a8-4cd6-b39b-7c41dada3471

import Mathlib

/-- Counterexample: the feasible set `X` is not assumed convex. Take `E = ℝ`, `X = {0, 1}`,
`V x z = (z - x)^2 / 2` with `dV x y = (y - x) • id`, `xt = 0`, `xt1 = 1`,
`gt = (-3/4) • id`, `γt = 1`. Then `xt1` minimizes `u ↦ gt u + V 0 u` over `X`
(values `0` at `u = 0` and `-1/4` at `u = 1`), but at `x = 0` the conclusion reads
`-1/4 ≤ -1/2`. -/
theorem solution : ¬ (∀ {E : Type} [NormedAddCommGroup E] [NormedSpace ℝ E]
    (X : Set E) (V : E → E → ℝ) (dV : E → E → E →L[ℝ] ℝ) (xt xt1 : E) (gt : E →L[ℝ] ℝ) (γt : ℝ)
    (hxt : xt ∈ X) (hxt1 : xt1 ∈ X)
    (hVnonneg : ∀ x ∈ X, ∀ z ∈ X, 0 ≤ V x z)
    (hVthreepoint : ∀ x ∈ X, ∀ y ∈ X, ∀ z ∈ X, V x z = V x y + (dV x y) (z - y) + V y z)
    (hmin : ∀ x ∈ X, γt * gt xt1 + V xt xt1 ≤ γt * gt x + V xt x),
    ∀ x ∈ X, γt * gt (xt1 - x) + V xt xt1 ≤ V xt x - V xt1 x) := by
  intro H
  have := H (E := ℝ) ({0, 1} : Set ℝ) (fun x z => (z - x) ^ 2 / 2)
    (fun x y => (y - x) • ContinuousLinearMap.id ℝ ℝ) 0 1
    ((-3 / 4 : ℝ) • ContinuousLinearMap.id ℝ ℝ) 1
    (by simp) (by simp)
    (fun x _ z _ => by positivity)
    (fun x _ y _ z _ => by simp; ring)
    (fun x hx => by
      rcases hx with rfl | rfl <;> simp <;> norm_num)
    0 (by simp)
  norm_num at this
