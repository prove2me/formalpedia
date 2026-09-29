-- Prove2me | solution 1 for CubicNewton.GradDom.grad_inner_step_nonneg
-- status  : ACCEPTED   (prove)
-- author  : @mrfancypants
-- created : 2026-09-29T00:17:36.994805+00:00
-- url     : https://prove2.me/submissions/76e4a9f8-c880-4ee3-99d7-8430855d5350

import Mathlib
import Definitions.Def_CubicNewton_Shared_IsCubicStep

open scoped RealInnerProductSpace

namespace CubicNewton.GradDom

theorem aux_gisn_key {n : ℕ}
    (g : EuclideanSpace ℝ (Fin n) → EuclideanSpace ℝ (Fin n))
    (H : EuclideanSpace ℝ (Fin n) → EuclideanSpace ℝ (Fin n) →L[ℝ] EuclideanSpace ℝ (Fin n))
    (M : ℝ) (x T : EuclideanSpace ℝ (Fin n))
    (hT : CubicNewton.Shared.IsCubicStep g H M x T) :
    0 ≤ ⟪g x, x - T⟫ := by
  have h1 := hT (x - (T - x))
  unfold CubicNewton.Shared.cubicModel at h1
  have e1 : x - (T - x) - x = -(T - x) := by abel
  have e2 : x - T = -(T - x) := by abel
  rw [e1, map_neg, inner_neg_neg, norm_neg, inner_neg_right] at h1
  rw [e2, inner_neg_right]
  linarith

end CubicNewton.GradDom

open CubicNewton.GradDom
open scoped RealInnerProductSpace

theorem solution {n : ℕ}
    (F : Set (EuclideanSpace ℝ (Fin n))) (f : EuclideanSpace ℝ (Fin n) → ℝ)
    (g : EuclideanSpace ℝ (Fin n) → EuclideanSpace ℝ (Fin n))
    (H : EuclideanSpace ℝ (Fin n) → EuclideanSpace ℝ (Fin n) →L[ℝ] EuclideanSpace ℝ (Fin n))
    (L : ℝ)
    (hF_closed : IsClosed F) (hF_convex : Convex ℝ F)
    (hf : ∀ x ∈ F, HasGradientAt f (g x) x) (hg : ∀ x ∈ F, HasFDerivAt g (H x) x)
    (hL : 0 < L) (hLip : ∀ x ∈ F, ∀ y ∈ F, ‖H x - H y‖ ≤ L * ‖x - y‖)
    (x₀ : EuclideanSpace ℝ (Fin n)) (hx₀ : x₀ ∈ interior F)
    (hlevel : {x | f x ≤ f x₀} ⊆ interior F)
    (M : ℝ) (hM : 0 < M) (x T : EuclideanSpace ℝ (Fin n)) (hx : x ∈ F) (hfx : f x ≤ f x₀)
    (hT : CubicNewton.Shared.IsCubicStep g H M x T) :
    0 ≤ ⟪g x, x - T⟫ := aux_gisn_key g H M x T hT
