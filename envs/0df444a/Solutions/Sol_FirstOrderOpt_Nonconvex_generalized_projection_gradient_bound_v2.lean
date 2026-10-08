-- Prove2me | solution 1 for FirstOrderOpt.Nonconvex.generalized_projection_gradient_bound_v2
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-07T04:41:08.208588+00:00
-- url     : https://prove2.me/submissions/6694e11f-fbad-4036-9316-95f45c1a5937

import Mathlib
import Definitions.Def_FirstOrderOpt_Prox_DistanceGeneratingFunction

set_option autoImplicit false

/-- If `a ≤ c * t` for every `t ∈ (0, 1)` with `c ≥ 0`, then `a ≤ 0`. -/
theorem gpgb294_le_zero_of_forall {a c : ℝ} (hc : 0 ≤ c)
    (H : ∀ t : ℝ, 0 < t → t < 1 → a ≤ c * t) : a ≤ 0 := by
  by_contra hneg
  replace hneg := lt_of_not_ge hneg
  set t : ℝ := min (1 / 2) (a / (2 * (c + 1))) with ht
  have hc1 : 0 < c + 1 := by linarith
  have ht0 : 0 < t := lt_min (by norm_num) (div_pos hneg (by positivity))
  have ht1 : t < 1 := lt_of_le_of_lt (min_le_left _ _) (by norm_num)
  have ht2 : t ≤ a / (2 * (c + 1)) := min_le_right _ _
  have h1 := H t ht0 ht1
  have h3 : t * (2 * (c + 1)) ≤ a := by
    rw [le_div_iff₀ (by positivity)] at ht2; linarith
  nlinarith

open FirstOrderOpt.Prox RealInnerProductSpace in
theorem solution {E : Type*} [NormedAddCommGroup E]
    [InnerProductSpace ℝ E]
    (X : Set E) (hXconv : Convex ℝ X) (hXclosed : IsClosed X)
    (h : E → ℝ) (hhconv : ConvexOn ℝ X h)
    (ν : DistanceGeneratingFunction X)
    (x xPlus g : E) (γ : ℝ) (hγ : 0 < γ) (hx : x ∈ X) (hxPlus : xPlus ∈ X)
    (hmin : ∀ u ∈ X, ⟪g, xPlus⟫ + (1 / γ) * ν.V x xPlus + h xPlus ≤
      ⟪g, u⟫ + (1 / γ) * ν.V x u + h u)
    (PXval : E) (hPX : PXval = (1 / γ) • (x - xPlus)) :
    ⟪g, PXval⟫ ≥ ‖PXval‖ ^ 2 + (1 / γ) * (h xPlus - h x) := by
  have hk0 : 0 < 1 / γ := by positivity
  set k : ℝ := 1 / γ with hk
  set d : E := xPlus - x with hd
  set n : ℝ := ‖d‖ with hn
  have key : ∀ t : ℝ, 0 < t → t < 1 →
      ⟪g, xPlus⟫ - ⟪g, x⟫ + h xPlus - h x + k * n ^ 2 ≤ (k * n ^ 2 / 2) * t := by
    intro t ht0 ht1
    set u : E := (1 - t) • xPlus + t • x with hu
    have huX : u ∈ X := hXconv hxPlus hx (by linarith) ht0.le (by ring)
    have e1 : xPlus - u = t • d := by rw [hu, hd]; module
    have e2 : x - u = (-(1 - t)) • d := by rw [hu, hd]; module
    have e3 : u - x = (1 - t) • d := by rw [hu, hd]; module
    have hmu := hmin u huX
    have hhu : h u ≤ (1 - t) * h xPlus + t * h x := by
      have := hhconv.2 hxPlus hx (by linarith : (0:ℝ) ≤ 1 - t) ht0.le (by ring)
      simpa [smul_eq_mul] using this
    have sc1 := ν.strongConvex u huX xPlus hxPlus
    have sc2 := ν.strongConvex u huX x hx
    have sc3 := ν.strongConvex x hx xPlus hxPlus
    have ginner : ⟪g, u⟫ = (1 - t) * ⟪g, xPlus⟫ + t * ⟪g, x⟫ := by
      rw [hu, inner_add_right, real_inner_smul_right, real_inner_smul_right]
    unfold DistanceGeneratingFunction.V at hmu
    rw [e1, norm_smul, map_smul] at sc1
    rw [e2, norm_smul, map_smul] at sc2
    rw [e3, map_smul, ginner] at hmu
    rw [← hd] at sc3 hmu
    rw [← hn] at sc1 sc2 sc3
    simp only [Real.norm_eq_abs, smul_eq_mul, mul_pow, sq_abs] at sc1 sc2 sc3 hmu
    have A : ν.ω u + 1 / 2 * (t * (1 - t) * n ^ 2) ≤ (1 - t) * ν.ω xPlus + t * ν.ω x := by
      nlinarith [mul_le_mul_of_nonneg_left sc1 (by linarith : (0:ℝ) ≤ 1 - t),
        mul_le_mul_of_nonneg_left sc2 ht0.le]
    have B : t * (ν.dω x d) + t * n ^ 2 - 1 / 2 * t ^ 2 * n ^ 2 ≤
        ν.ω xPlus - ν.ω u - t * (ν.dω x d) + t * (ν.dω x d) := by
      nlinarith [mul_le_mul_of_nonneg_left sc3 ht0.le]
    have C : t * (⟪g, xPlus⟫ - ⟪g, x⟫) + k * (ν.ω xPlus - ν.ω u - t * (ν.dω x d))
        + t * (h xPlus - h x) ≤ 0 := by
      nlinarith
    have D : k * (t * n ^ 2 - 1 / 2 * t ^ 2 * n ^ 2) ≤
        k * (ν.ω xPlus - ν.ω u - t * (ν.dω x d)) :=
      mul_le_mul_of_nonneg_left (by linarith) hk0.le
    have E' : t * (⟪g, xPlus⟫ - ⟪g, x⟫ + h xPlus - h x + k * n ^ 2 - (k * n ^ 2 / 2) * t)
        ≤ 0 := by nlinarith
    have hb : ⟪g, xPlus⟫ - ⟪g, x⟫ + h xPlus - h x + k * n ^ 2 - (k * n ^ 2 / 2) * t ≤ 0 := by
      by_contra hc
      have hc' := mul_pos ht0 (lt_of_not_ge hc)
      linarith
    linarith
  have hfin : ⟪g, xPlus⟫ - ⟪g, x⟫ + h xPlus - h x + k * n ^ 2 ≤ 0 := by
    have := gpgb294_le_zero_of_forall (a := ⟪g, xPlus⟫ - ⟪g, x⟫ + h xPlus - h x + k * n ^ 2)
      (c := k * n ^ 2 / 2) (by positivity) key
    exact this
  have hnorm : ‖x - xPlus‖ = n := by rw [hn, hd, norm_sub_rev]
  rw [hPX, real_inner_smul_right, norm_smul, inner_sub_right, hnorm, Real.norm_eq_abs,
    abs_of_pos hk0]
  nlinarith [mul_le_mul_of_nonneg_left hfin hk0.le]
