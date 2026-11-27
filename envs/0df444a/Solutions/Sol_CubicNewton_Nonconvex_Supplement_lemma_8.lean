-- Prove2me | solution 1 for CubicNewton.Nonconvex.Supplement.lemma_8
-- status  : ACCEPTED   (prove)
-- author  : @mikedeng1
-- created : 2026-11-27T06:39:12.045989+00:00
-- url     : https://prove2.me/submissions/204c568f-5710-4cbc-87f2-3a71657f5f7b

import Mathlib
import Definitions.Def_CubicNewton_Nonconvex_Supplement_TransformedConvexSetting

open CubicNewton
open CubicNewton.Nonconvex
open CubicNewton.Nonconvex.Supplement

/-- Nesterov–Polyak 2006, Lemma 8, (4.18), p. 195. In the setting of Section 4.3
(`f = φ ∘ u`, `v` the inverse of `u`, `σ` a bound on `‖v′‖` over `{z : φ(z) ≤ f(x₀)}`),
for any `x, y ∈ L(f(x₀))` we have `‖x − y‖ ≤ σ ‖u(x) − u(y)‖`. -/
theorem solution {n : ℕ} (f : EuclideanSpace ℝ (Fin n) → ℝ) (x₀ : EuclideanSpace ℝ (Fin n))
    (φ : EuclideanSpace ℝ (Fin n) → ℝ) (u v : EuclideanSpace ℝ (Fin n) → EuclideanSpace ℝ (Fin n))
    (v' : EuclideanSpace ℝ (Fin n) → EuclideanSpace ℝ (Fin n) →L[ℝ] EuclideanSpace ℝ (Fin n))
    (ustar : EuclideanSpace ℝ (Fin n)) (σ D : ℝ)
    (hT : TransformedConvexSetting f x₀ φ u v v' ustar σ D) :
    ∀ x y : EuclideanSpace ℝ (Fin n), f x ≤ f x₀ → f y ≤ f x₀ →
      ‖x - y‖ ≤ σ * ‖u x - u y‖ := by
        intro x y hx hy
        have hconv : Convex ℝ {z | φ z ≤ f x₀} := by
          simpa only [Set.mem_univ, true_and] using hT.convex.convex_le (f x₀)
        have hx' : u x ∈ {z | φ z ≤ f x₀} := by
          change φ (u x) ≤ f x₀
          rw [← hT.comp x]
          exact hx
        have hy' : u y ∈ {z | φ z ≤ f x₀} := by
          change φ (u y) ≤ f x₀
          rw [← hT.comp y]
          exact hy
        have hderiv : ∀ z ∈ {z | φ z ≤ f x₀},
            HasFDerivWithinAt v (v' z) {z | φ z ≤ f x₀} z := by
          intro z hz
          exact (hT.hasDeriv_inv z hz).hasFDerivWithinAt
        have hbound : ∀ z ∈ {z | φ z ≤ f x₀}, ‖v' z‖ ≤ σ := by
          intro z hz
          exact hT.sigma_bound z hz
        have hmean := hconv.norm_image_sub_le_of_norm_hasFDerivWithin_le hderiv hbound hy' hx'
        simpa only [hT.left_inv] using hmean
