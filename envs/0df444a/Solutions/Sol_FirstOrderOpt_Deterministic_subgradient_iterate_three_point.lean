-- Prove2me | solution 1 for FirstOrderOpt.Deterministic.subgradient_iterate_three_point
-- status  : ACCEPTED   (disprove)
-- author  : @mrfancypants
-- created : 2026-09-28T22:27:41.42402+00:00
-- url     : https://prove2.me/submissions/0ec7abf7-e3aa-4b63-80a4-255d242f0c81

import Mathlib

namespace FirstOrderOpt.Deterministic

open scoped RealInnerProductSpace

/-- Core counterexample: in any real inner product space containing a unit vector `e`, take
`X = {0, 5 • e}`, `xt = 2 • e`, `xt1 = 0`, `gt = 0`, `γt = 1`. -/
theorem aux_sitp_counterexample {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    (e : E) (he : ‖e‖ = 1) :
    ¬ (∀ (X : Set E) (xt xt1 gt : E) (γt : ℝ)
    (_hxt1 : xt1 ∈ X)
    (_hmin : ∀ x ∈ X, γt * ⟪gt, xt1⟫ + (1 / 2) * ‖xt1 - xt‖ ^ 2 ≤
      γt * ⟪gt, x⟫ + (1 / 2) * ‖x - xt‖ ^ 2),
    ∀ x ∈ X, γt * ⟪gt, xt1 - x⟫ + (1 / 2) * ‖xt1 - xt‖ ^ 2 ≤
      (1 / 2) * ‖x - xt‖ ^ 2 - (1 / 2) * ‖x - xt1‖ ^ 2) := by
  intro H
  have h02 : ‖(0 : E) - (2 : ℝ) • e‖ = 2 := by
    rw [zero_sub, norm_neg, norm_smul, he]; norm_num
  have h52 : ‖(5 : ℝ) • e - (2 : ℝ) • e‖ = 3 := by
    rw [← sub_smul, norm_smul, he]; norm_num
  have h50 : ‖(5 : ℝ) • e - 0‖ = 5 := by
    rw [sub_zero, norm_smul, he]; norm_num
  have hmin : ∀ x ∈ ({0, (5 : ℝ) • e} : Set E),
      (1 : ℝ) * ⟪(0 : E), (0 : E)⟫ + (1 / 2) * ‖(0 : E) - (2 : ℝ) • e‖ ^ 2 ≤
      (1 : ℝ) * ⟪(0 : E), x⟫ + (1 / 2) * ‖x - (2 : ℝ) • e‖ ^ 2 := by
    intro x hx
    rcases hx with rfl | hx
    · exact le_refl _
    · rw [Set.mem_singleton_iff] at hx
      subst hx
      rw [h02, h52, inner_zero_left, inner_zero_left]
      norm_num
  have := H {0, (5 : ℝ) • e} ((2 : ℝ) • e) 0 0 1 (Or.inl rfl) hmin ((5 : ℝ) • e)
    (Or.inr rfl)
  rw [inner_zero_left, h02, h52, h50] at this
  norm_num at this

end FirstOrderOpt.Deterministic

open FirstOrderOpt.Deterministic
open scoped RealInnerProductSpace

theorem solution : ¬ (∀ {E : Type} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    (X : Set E) (xt xt1 gt : E) (γt : ℝ)
    (hxt1 : xt1 ∈ X)
    (hmin : ∀ x ∈ X, γt * ⟪gt, xt1⟫ + (1 / 2) * ‖xt1 - xt‖ ^ 2 ≤
      γt * ⟪gt, x⟫ + (1 / 2) * ‖x - xt‖ ^ 2),
    ∀ x ∈ X, γt * ⟪gt, xt1 - x⟫ + (1 / 2) * ‖xt1 - xt‖ ^ 2 ≤
      (1 / 2) * ‖x - xt‖ ^ 2 - (1 / 2) * ‖x - xt1‖ ^ 2) := by
  intro H
  exact aux_sitp_counterexample
    (EuclideanSpace.single (0 : Fin 1) (1 : ℝ))
    (by rw [EuclideanSpace.norm_single]; norm_num)
    (fun X xt xt1 gt γt hxt1 hmin => H X xt xt1 gt γt hxt1 hmin)
