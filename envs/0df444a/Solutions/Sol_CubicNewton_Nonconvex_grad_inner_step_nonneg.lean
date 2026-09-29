-- Prove2me | solution 1 for CubicNewton.Nonconvex.grad_inner_step_nonneg
-- status  : ACCEPTED   (prove)
-- author  : @mrfancypants
-- created : 2026-09-28T22:18:58.145048+00:00
-- url     : https://prove2.me/submissions/4dfd99da-a533-4ed3-a6fd-43800ddd44f4

import Mathlib
import Definitions.Def_CubicNewton_Shared_IsCubicStep

open scoped RealInnerProductSpace

namespace CubicNewton.Nonconvex

theorem aux_gisn_key {n : ℕ}
    (g : EuclideanSpace ℝ (Fin n) → EuclideanSpace ℝ (Fin n))
    (H : EuclideanSpace ℝ (Fin n) → EuclideanSpace ℝ (Fin n) →L[ℝ] EuclideanSpace ℝ (Fin n))
    (M : ℝ) (x T : EuclideanSpace ℝ (Fin n))
    (hT : CubicNewton.Shared.IsCubicStep g H M x T) :
    0 ≤ ⟪g x, x - T⟫ := by
  have h := hT (x - (T - x))
  unfold CubicNewton.Shared.cubicModel at h
  have e1 : x - (T - x) - x = -(T - x) := by abel
  rw [e1, map_neg, inner_neg_neg, norm_neg, inner_neg_right] at h
  have e2 : x - T = -(T - x) := by abel
  rw [e2, inner_neg_right]
  linarith

end CubicNewton.Nonconvex

open CubicNewton.Nonconvex
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
    0 ≤ ⟪g x, x - T⟫ :=
  aux_gisn_key g H M x T hT
