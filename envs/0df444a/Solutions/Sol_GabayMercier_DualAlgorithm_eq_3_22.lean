-- Prove2me | solution 1 for GabayMercier.DualAlgorithm.eq_3_22
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-07T01:36:20.382345+00:00
-- url     : https://prove2.me/submissions/56361413-15ce-4b7b-b08b-dd5d62bf835c

import Mathlib
import Definitions.Def_InertialFB_IFB_ConvexAnalysis
import Definitions.Def_GabayMercier_DualAlgorithm_Model

set_option autoImplicit false

open Filter Topology InertialFB.IFB

namespace GabayMercier.DualAlgorithm.P27147d11

variable {V Y : Type*} [NormedAddCommGroup V] [InnerProductSpace ℝ V] [CompleteSpace V]
  [NormedAddCommGroup Y] [InnerProductSpace ℝ Y] [CompleteSpace Y]

/-- From the saddle point: `A* λ* = b`. -/
theorem adj_eq (A : V →L[ℝ] Y) (f₁ : Y → ℝ) (f₁' : Y → Y) (f₂ : Y → EReal)
    (b : StrongDual ℝ V) (γ α : ℝ) (h : StandingHyp A f₁ f₁' f₂ γ α)
    (vs : V) (ys ls : Y) (hsp : IsSaddlePoint (lagrangian A f₁ f₂ b) vs ys ls) :
    ∀ w, inner ℝ ls (A w) = b w := by
  have hprop := h.f₂_proper
  have hne_top : f₂ ys ≠ ⊤ := by
    intro htop
    obtain ⟨z, hz⟩ := hprop.2
    have hh := hsp.2 vs z
    rw [lagrangian, lagrangian, htop, EReal.coe_add_top,
      ← EReal.coe_toReal hz (hprop.1 z), ← EReal.coe_add] at hh
    exact EReal.coe_ne_top _ (top_le_iff.mp hh)
  have ht := EReal.coe_toReal hne_top (hprop.1 ys)
  have hle : ∀ w, inner ℝ ls (A vs - ys) - b vs ≤ inner ℝ ls (A w - ys) - b w := by
    intro w
    have hh := hsp.2 w ys
    rw [lagrangian, lagrangian, ← ht, ← EReal.coe_add, ← EReal.coe_add,
      EReal.coe_le_coe_iff] at hh
    linarith
  intro u
  have h1 := hle (vs + u)
  have h2 := hle (vs - u)
  simp only [map_add, map_sub, inner_add_right, inner_sub_right] at h1 h2
  linarith

end GabayMercier.DualAlgorithm.P27147d11

open GabayMercier.DualAlgorithm in
theorem solution {V Y : Type*} [NormedAddCommGroup V] [InnerProductSpace ℝ V] [CompleteSpace V]
    [NormedAddCommGroup Y] [InnerProductSpace ℝ Y] [CompleteSpace Y]
    (A : V →L[ℝ] Y) (f₁ : Y → ℝ) (f₁' : Y → Y) (f₂ : Y → EReal)
    (b : StrongDual ℝ V) (γ α : ℝ) (h : StandingHyp A f₁ f₁' f₂ γ α) (r ρ : ℝ) (hr : 0 < r)
    (hρ : 0 < ρ) (v : ℕ → V) (y lam : ℕ → Y) (hrun : IsModifiedDualRun A f₁' f₂ b r ρ v y lam)
    (vs : V) (ys ls : Y) (hsp : IsSaddlePoint (lagrangian A f₁ f₂ b) vs ys ls) :
    ∀ ε : ℝ, 0 < ε → ∀ n : ℕ,
      ‖projRange A (lam (n + 1) - ls)‖ ^ 2 ≤
        ((1 - ρ / r) ^ 2 + ρ * ε * |1 - ρ / r|) * ‖projRange A (lam n - ls)‖ ^ 2
          + (ρ ^ 2 + |1 - ρ / r| * ρ / ε) * ‖projRange A (y (n + 1) - y n)‖ ^ 2 := by
  intro ε hε n
  obtain ⟨h1, -, h3⟩ := hrun n
  have hadj := GabayMercier.DualAlgorithm.P27147d11.adj_eq A f₁ f₁' f₂ b γ α h vs ys ls hsp
  have horth : r • (A (v (n + 1)) - y n) + (lam n - ls) ∈
      (LinearMap.range (A : V →ₗ[ℝ] Y))ᗮ := by
    rw [Submodule.mem_orthogonal]
    rintro _ ⟨w, rfl⟩
    have e1 := h1 w
    rw [inner_sub_left, real_inner_smul_left] at e1
    have e2 := hadj w
    simp only [ContinuousLinearMap.coe_coe, inner_add_right, inner_sub_right,
      real_inner_smul_right]
    rw [real_inner_comm (A (v (n + 1))) (A w), real_inner_comm (y n) (A w),
      real_inner_comm (lam n) (A w), real_inner_comm ls (A w)]
    linarith
  have hP0 : projRange A (r • (A (v (n + 1)) - y n) + (lam n - ls)) = 0 := by
    show (LinearMap.range (A : V →ₗ[ℝ] Y)).topologicalClosure.starProjection _ = 0
    rw [Submodule.starProjection_apply_eq_zero_iff, Submodule.orthogonal_closure]
    exact horth
  have hPA : projRange A (A (v (n + 1))) = A (v (n + 1)) := by
    show (LinearMap.range (A : V →ₗ[ℝ] Y)).topologicalClosure.starProjection _ = _
    rw [Submodule.starProjection_eq_self_iff]
    exact Submodule.le_topologicalClosure _ ⟨v (n + 1), rfl⟩
  have hX : projRange A (lam (n + 1) - ls) =
      (1 - ρ / r) • projRange A (lam n - ls) - ρ • projRange A (y (n + 1) - y n) := by
    rw [h3]
    have e : lam n + ρ • (A (v (n + 1)) - y (n + 1)) - ls
        = (lam n - ls) + ρ • (A (v (n + 1)) - y (n + 1)) := by abel
    rw [e, map_add, map_smul, map_sub (projRange A) (A (v (n + 1))) (y (n + 1)), hPA,
      map_sub (projRange A) (y (n + 1)) (y n)]
    rw [map_add, map_smul, map_sub (projRange A) (A (v (n + 1))) (y n), hPA] at hP0
    set a := projRange A (lam n - ls)
    set u := A (v (n + 1))
    set p := projRange A (y n)
    set q := projRange A (y (n + 1))
    have hu : u = p - r⁻¹ • a := by
      have h4 : r • (u - p) = -a := eq_neg_of_add_eq_zero_left hP0
      have h5 := congrArg (fun z => r⁻¹ • z) h4
      simp only [smul_smul, inv_mul_cancel₀ hr.ne', one_smul, smul_neg] at h5
      rw [sub_eq_iff_eq_add] at h5
      rw [h5]; abel
    rw [hu]
    simp only [div_eq_mul_inv]
    module
  rw [hX]
  set a := projRange A (lam n - ls)
  set d := projRange A (y (n + 1) - y n)
  set θ := ρ / r
  have e : ‖(1 - θ) • a - ρ • d‖ ^ 2
      = (1 - θ) ^ 2 * ‖a‖ ^ 2 - 2 * ((1 - θ) * ρ) * inner ℝ a d + ρ ^ 2 * ‖d‖ ^ 2 := by
    rw [norm_sub_sq_real, norm_smul, norm_smul, real_inner_smul_left, real_inner_smul_right,
      Real.norm_eq_abs, Real.norm_eq_abs, mul_pow, mul_pow, sq_abs, sq_abs]
    ring
  have hcs : |inner ℝ a d| ≤ ‖a‖ * ‖d‖ := abs_real_inner_le_norm a d
  have h2 : 2 * ‖a‖ * ‖d‖ ≤ ε * ‖a‖ ^ 2 + ‖d‖ ^ 2 / ε := by
    rw [← sub_nonneg]
    have h6 : ε * ‖a‖ ^ 2 + ‖d‖ ^ 2 / ε - 2 * ‖a‖ * ‖d‖ = (ε * ‖a‖ - ‖d‖) ^ 2 / ε := by
      field_simp
      ring
    rw [h6]
    positivity
  have h7 : -((1 - θ) * inner ℝ a d) ≤ |1 - θ| * (‖a‖ * ‖d‖) :=
    calc -((1 - θ) * inner ℝ a d) ≤ |(1 - θ) * inner ℝ a d| := neg_le_abs _
      _ = |1 - θ| * |inner ℝ a d| := abs_mul _ _
      _ ≤ |1 - θ| * (‖a‖ * ‖d‖) := mul_le_mul_of_nonneg_left hcs (abs_nonneg _)
  have h8 : -(2 * ((1 - θ) * ρ) * inner ℝ a d) ≤ |1 - θ| * ρ * (2 * ‖a‖ * ‖d‖) := by
    have := mul_le_mul_of_nonneg_left h7 (by positivity : (0:ℝ) ≤ 2 * ρ)
    linarith
  have h9 := mul_le_mul_of_nonneg_left h2 (by positivity : (0:ℝ) ≤ |1 - θ| * ρ)
  rw [e]
  have h10 : |1 - θ| * ρ * (ε * ‖a‖ ^ 2 + ‖d‖ ^ 2 / ε)
      = ρ * ε * |1 - θ| * ‖a‖ ^ 2 + |1 - θ| * ρ / ε * ‖d‖ ^ 2 := by ring
  nlinarith [h8, h9, h10]
