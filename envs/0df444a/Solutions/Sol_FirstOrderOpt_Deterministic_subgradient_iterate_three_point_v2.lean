-- Prove2me | solution 1 for FirstOrderOpt.Deterministic.subgradient_iterate_three_point_v2
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-06T18:54:13.458974+00:00
-- url     : https://prove2.me/submissions/c36c24be-eee7-4bfb-b629-fe223829601f

import Mathlib

set_option autoImplicit false

theorem cdc7f712_limit_aux (c K : ℝ) (hK : 0 ≤ K)
    (h : ∀ s : ℝ, 0 < s → s ≤ 1 → 0 ≤ c + s / 2 * K) : 0 ≤ c := by
  by_contra hc
  rw [not_le] at hc
  have hK1 : 0 < K + 1 := by linarith
  have hs0 : 0 < min 1 (-c / (K + 1)) := lt_min one_pos (div_pos (by linarith) hK1)
  have hs1 : min 1 (-c / (K + 1)) ≤ 1 := min_le_left _ _
  have hs2 : min 1 (-c / (K + 1)) ≤ -c / (K + 1) := min_le_right _ _
  have h1 := h _ hs0 hs1
  have h3 : min 1 (-c / (K + 1)) * (K + 1) ≤ -c := by rwa [le_div_iff₀ hK1] at hs2
  nlinarith

open scoped RealInnerProductSpace in
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
  have hstep : ∀ s : ℝ, 0 < s → s ≤ 1 →
      0 ≤ (γt * ⟪gt, x - xt1⟫ + ⟪xt1 - xt, x - xt1⟫) + s / 2 * ‖x - xt1‖ ^ 2 := by
    intro s hs0 hs1
    have hmem : xt1 + s • (x - xt1) ∈ X := hXconv.add_smul_sub_mem hxt1 hx ⟨hs0.le, hs1⟩
    have h := hmin _ hmem
    have e1 : xt1 + s • (x - xt1) - xt = (xt1 - xt) + s • (x - xt1) := by abel
    rw [e1, inner_add_right, inner_smul_right, norm_add_sq_real, inner_smul_right,
      norm_smul, Real.norm_eq_abs, abs_of_pos hs0] at h
    nlinarith
  have hc := cdc7f712_limit_aux _ _ (by positivity) hstep
  have e2 : x - xt = (x - xt1) + (xt1 - xt) := by abel
  have e3 : xt1 - x = -(x - xt1) := by abel
  rw [e2, e3, inner_neg_right, norm_add_sq_real, real_inner_comm (xt1 - xt)] at *
  nlinarith
