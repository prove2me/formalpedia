-- Prove2me | solution 2 for FirstOrderOpt.Deterministic.subgradient_iterate_three_point_v2
-- status  : ACCEPTED   (prove)
-- author  : @savarin
-- created : 2026-10-10T04:11:02.083838+00:00
-- url     : https://prove2.me/submissions/b0be543a-5476-42a0-8817-7849b79e287b

import Mathlib

open scoped RealInnerProductSpace

theorem solution {E : Type*} [NormedAddCommGroup E]
    [InnerProductSpace ℝ E]
    (X : Set E) (hXconv : Convex ℝ X) (hXclosed : IsClosed X)
    (xt xt1 gt : E) (γt : ℝ)
    (hxt : xt ∈ X) (hxt1 : xt1 ∈ X)
    (hmin : ∀ x ∈ X, γt * ⟪gt, xt1⟫ + (1 / 2) * ‖xt1 - xt‖ ^ 2 ≤
      γt * ⟪gt, x⟫ + (1 / 2) * ‖x - xt‖ ^ 2) :
    ∀ x ∈ X, γt * ⟪gt, xt1 - x⟫ + (1 / 2) * ‖xt1 - xt‖ ^ 2 ≤
      (1 / 2) * ‖x - xt‖ ^ 2 - (1 / 2) * ‖x - xt1‖ ^ 2 := by
  intro x hx
  have key : ∀ s : ℝ, 0 < s → s ≤ 1 →
      0 ≤ s * (γt * ⟪gt, x - xt1⟫ + ⟪xt1 - xt, x - xt1⟫) + s ^ 2 / 2 * ‖x - xt1‖ ^ 2 := by
    intro s hs0 hs1
    have hy : xt1 + s • (x - xt1) ∈ X := by
      have := hXconv hxt1 hx (by linarith : (0:ℝ) ≤ 1 - s) hs0.le (by ring)
      convert this using 1
      rw [smul_sub, sub_smul, one_smul]; abel
    have h := hmin _ hy
    have e1 : xt1 + s • (x - xt1) - xt = (xt1 - xt) + s • (x - xt1) := by abel
    rw [e1, norm_add_sq_real, inner_add_right, inner_smul_right, inner_smul_right, norm_smul,
      mul_pow, Real.norm_eq_abs, sq_abs] at h
    nlinarith
  have hA : 0 ≤ γt * ⟪gt, x - xt1⟫ + ⟪xt1 - xt, x - xt1⟫ := by
    by_contra hneg
    push_neg at hneg
    set A := γt * ⟪gt, x - xt1⟫ + ⟪xt1 - xt, x - xt1⟫
    set B := ‖x - xt1‖ ^ 2
    have hB : 0 ≤ B := by positivity
    set s := min 1 (-A / (B + 1))
    have hs0 : 0 < s := lt_min one_pos (div_pos (by linarith) (by linarith))
    have hs1 : s ≤ 1 := min_le_left _ _
    have hs2 : s * (B + 1) ≤ -A := by
      have := min_le_right 1 (-A / (B + 1))
      rwa [le_div_iff₀ (by linarith)] at this
    have := key s hs0 hs1
    nlinarith [mul_pos hs0 hs0]
  have e2 : x - xt = (xt1 - xt) + (x - xt1) := by abel
  have e3 : xt1 - x = -(x - xt1) := by abel
  rw [e2, norm_add_sq_real, e3, inner_neg_right]
  nlinarith [real_inner_comm (xt1 - xt) (x - xt1)]
