-- Prove2me | solution 1 for FirstOrderOpt.Deterministic.subgradient_descent_bound_v2
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-07T05:32:13.836301+00:00
-- url     : https://prove2.me/submissions/2cff6dda-699e-4f8c-96dd-902563a38a37

import Mathlib

set_option autoImplicit false

theorem p09af8c30_limit_aux (c K : ℝ) (hK : 0 ≤ K)
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
theorem p09af8c30_three_point {E : Type*} [NormedAddCommGroup E]
    [InnerProductSpace ℝ E]
    (X : Set E) (hXconv : Convex ℝ X)
    (xt xt1 gt : E) (γt : ℝ)
    (hxt1 : xt1 ∈ X)
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
  have hc := p09af8c30_limit_aux _ _ (by positivity) hstep
  have e2 : x - xt = (x - xt1) + (xt1 - xt) := by abel
  have e3 : xt1 - x = -(x - xt1) := by abel
  rw [e2, e3, inner_neg_right, norm_add_sq_real, real_inner_comm (xt1 - xt)] at *
  nlinarith

open scoped RealInnerProductSpace in
theorem p09af8c30_step {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    (X : Set E) (hXconv : Convex ℝ X)
    (f : E → ℝ) (M : ℝ)
    (xt xt1 gt x' : E) (γt : ℝ) (hx' : x' ∈ X)
    (hxt1 : xt1 ∈ X) (hγ : 0 < γt)
    (hsub : f xt + ⟪gt, x' - xt⟫ ≤ f x')
    (hgnorm : ‖gt‖ ≤ M)
    (hmin : ∀ y ∈ X, γt * ⟪gt, xt1⟫ + (1 / 2) * ‖xt1 - xt‖ ^ 2 ≤
      γt * ⟪gt, y⟫ + (1 / 2) * ‖y - xt‖ ^ 2) :
    γt * (f xt - f x') ≤ (1 / 2) * ‖x' - xt‖ ^ 2 - (1 / 2) * ‖x' - xt1‖ ^ 2
      + M ^ 2 / 2 * γt ^ 2 := by
  have h3 := p09af8c30_three_point X hXconv xt xt1 gt γt hxt1 hmin x' hx'
  have hcs : ⟪gt, xt - xt1⟫ ≤ ‖gt‖ * ‖xt - xt1‖ := real_inner_le_norm _ _
  have hn : ‖xt - xt1‖ = ‖xt1 - xt‖ := norm_sub_rev _ _
  have hsplit : ⟪gt, x' - xt⟫ = -(⟪gt, xt - xt1⟫ + ⟪gt, xt1 - x'⟫) := by
    rw [← inner_add_right, ← inner_neg_right]; congr 1; abel
  have hnn : 0 ≤ ‖xt1 - xt‖ := norm_nonneg _
  have hgn : 0 ≤ ‖gt‖ := norm_nonneg _
  have hcs2 : ⟪gt, xt - xt1⟫ ≤ M * ‖xt1 - xt‖ := by
    rw [hn] at hcs; nlinarith
  rw [hsplit] at hsub
  have hA : f xt - f x' ≤ ⟪gt, xt - xt1⟫ + ⟪gt, xt1 - x'⟫ := by linarith
  have hB : γt * (f xt - f x') ≤ γt * ⟪gt, xt - xt1⟫ + γt * ⟪gt, xt1 - x'⟫ := by
    have := mul_le_mul_of_nonneg_left hA hγ.le; linarith
  have hC : γt * ⟪gt, xt - xt1⟫ ≤ γt * (M * ‖xt1 - xt‖) :=
    mul_le_mul_of_nonneg_left hcs2 hγ.le
  nlinarith [sq_nonneg (γt * M - ‖xt1 - xt‖)]

open scoped RealInnerProductSpace in
theorem solution {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    (X : Set E) (hXconv : Convex ℝ X) (hXclosed : IsClosed X)
    (f : E → ℝ) (hfconv : ConvexOn ℝ X f) (M : ℝ) (hM : 0 < M)
    (hLip : ∀ x ∈ X, ∀ y ∈ X, |f x - f y| ≤ M * ‖x - y‖)
    (x g : ℕ → E) (γ : ℕ → ℝ)
    (hx : ∀ t, x t ∈ X) (hγ : ∀ t, 0 < γ t)
    (hsub : ∀ t, ∀ y ∈ X, f (x t) + ⟪g t, y - x t⟫ ≤ f y)
    (hgnorm : ∀ t, ‖g t‖ ≤ M)
    (hmin : ∀ t, ∀ y ∈ X, γ t * ⟪g t, x (t + 1)⟫ + (1 / 2) * ‖x (t + 1) - x t‖ ^ 2 ≤
      γ t * ⟪g t, y⟫ + (1 / 2) * ‖y - x t‖ ^ 2)
    (s k : ℕ) (hsk : s ≤ k) :
    ∀ x' ∈ X, ∑ t ∈ Finset.Icc s k, γ t * (f (x t) - f x') ≤
      (1 / 2) * (‖x' - x s‖ ^ 2 + M ^ 2 * ∑ t ∈ Finset.Icc s k, (γ t) ^ 2) := by
  intro x' hx'
  have hstep : ∀ t, γ t * (f (x t) - f x') ≤ (1 / 2) * ‖x' - x t‖ ^ 2
      - (1 / 2) * ‖x' - x (t + 1)‖ ^ 2 + M ^ 2 / 2 * γ t ^ 2 := fun t =>
    p09af8c30_step X hXconv f M (x t) (x (t + 1)) (g t) x' (γ t) hx' (hx (t + 1)) (hγ t)
      (hsub t x' hx') (hgnorm t) (hmin t)
  have key : ∀ n, s ≤ n → ∑ t ∈ Finset.Icc s n, γ t * (f (x t) - f x') ≤
      (1 / 2) * ‖x' - x s‖ ^ 2 - (1 / 2) * ‖x' - x (n + 1)‖ ^ 2
        + M ^ 2 / 2 * ∑ t ∈ Finset.Icc s n, (γ t) ^ 2 := by
    intro n hn
    induction n, hn using Nat.le_induction with
    | base =>
      simp only [Finset.Icc_self, Finset.sum_singleton]
      linarith [hstep s]
    | succ n hn ih =>
      rw [Finset.sum_Icc_succ_top (by omega), Finset.sum_Icc_succ_top (by omega)]
      have := hstep (n + 1)
      nlinarith
  have := key k hsk
  have h0 : 0 ≤ ‖x' - x (k + 1)‖ ^ 2 := sq_nonneg _
  linarith
