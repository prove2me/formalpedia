-- Prove2me | solution 1 for CubicNewton.GradDom.cubicStep_hessian_psd
-- status  : ACCEPTED   (prove)
-- author  : @mrfancypants
-- created : 2026-09-29T00:18:46.622691+00:00
-- url     : https://prove2.me/submissions/331cb8cf-06a9-4ae3-85ee-f164feeb109c

import Mathlib
import Definitions.Def_CubicNewton_Shared_IsCubicStep

open scoped RealInnerProductSpace

namespace CubicNewton.GradDom

open Filter Topology

/-- First-order optimality condition for a global minimizer of the cubic model. -/
theorem aux_chp_first_order {n : ℕ}
    (g : EuclideanSpace ℝ (Fin n) → EuclideanSpace ℝ (Fin n))
    (H : EuclideanSpace ℝ (Fin n) → EuclideanSpace ℝ (Fin n) →L[ℝ] EuclideanSpace ℝ (Fin n))
    (M : ℝ) (x T : EuclideanSpace ℝ (Fin n))
    (hT : CubicNewton.Shared.IsCubicStep g H M x T) (w : EuclideanSpace ℝ (Fin n)) :
    ⟪g x, w⟫ + 1 / 2 * (⟪H x (T - x), w⟫ + ⟪H x w, T - x⟫) + M / 2 * ‖T - x‖ * ⟪T - x, w⟫
      = 0 := by
  set h := T - x with hh
  set A := H x with hA
  set G := g x with hG
  let u : ℝ → EuclideanSpace ℝ (Fin n) := fun t => h + t • w
  let φ : ℝ → ℝ := fun t => ⟪G, u t⟫ + 1 / 2 * ⟪A (u t), u t⟫ + M / 6 * ‖u t‖ ^ (3:ℝ)
  have hφ : ∀ t, φ t = CubicNewton.Shared.cubicModel g H M x (T + t • w) := by
    intro t
    have e : T + t • w - x = h + t • w := by rw [hh]; abel
    simp only [φ, u, CubicNewton.Shared.cubicModel, e]
    norm_cast
  have hmin : IsLocalMin φ 0 := by
    refine Filter.Eventually.of_forall (fun t => ?_)
    rw [hφ, hφ]
    simpa using hT (T + t • w)
  have hu : HasDerivAt u w 0 := by
    have := ((hasDerivAt_id (0:ℝ)).smul_const w).const_add h
    simpa [u] using this
  have hu0 : u 0 = h := by simp [u]
  have d1 : HasDerivAt (fun t => ⟪G, u t⟫) (⟪G, w⟫) 0 := by
    have := (hasDerivAt_const (0:ℝ) G).inner ℝ hu
    simpa using this
  have hAu : HasDerivAt (fun t => A (u t)) (A w) 0 := A.hasFDerivAt.comp_hasDerivAt 0 hu
  have d2 : HasDerivAt (fun t => ⟪A (u t), u t⟫) (⟪A h, w⟫ + ⟪A w, h⟫) 0 := by
    have := hAu.inner ℝ hu
    simpa [hu0] using this
  have d3 : HasDerivAt (fun t => ‖u t‖ ^ (3:ℝ)) (3 * ‖h‖ * ⟪h, w⟫) 0 := by
    have := (hasFDerivAt_norm_rpow (u 0) (p := 3) (by norm_num)).comp_hasDerivAt 0 hu
    refine this.congr_deriv ?_
    rw [hu0]
    simp only [ContinuousLinearMap.smul_apply, innerSL_apply_apply, smul_eq_mul]
    norm_num
  have hd : HasDerivAt φ
      (⟪G, w⟫ + 1 / 2 * (⟪A h, w⟫ + ⟪A w, h⟫) + M / 6 * (3 * ‖h‖ * ⟪h, w⟫)) 0 :=
    (d1.add (d2.const_mul (1 / 2))).add (d3.const_mul (M / 6))
  have := hmin.hasDerivAt_eq_zero hd
  linarith

end CubicNewton.GradDom

open CubicNewton.GradDom

open scoped RealInnerProductSpace

open Filter Topology

theorem solution {n : ℕ}
    (F : Set (EuclideanSpace ℝ (Fin n))) (f : EuclideanSpace ℝ (Fin n) → ℝ)
    (g : EuclideanSpace ℝ (Fin n) → EuclideanSpace ℝ (Fin n))
    (H : EuclideanSpace ℝ (Fin n) → EuclideanSpace ℝ (Fin n) →L[ℝ] EuclideanSpace ℝ (Fin n))
    (L : ℝ)
    (hF_closed : IsClosed F) (hF_convex : Convex ℝ F)
    (hF_int : (interior F).Nonempty)
    (hf : ∀ x ∈ F, HasGradientAt f (g x) x) (hg : ∀ x ∈ F, HasFDerivAt g (H x) x)
    (hL : 0 < L) (hLip : ∀ x ∈ F, ∀ y ∈ F, ‖H x - H y‖ ≤ L * ‖x - y‖)
    (M : ℝ) (hM : 0 < M) (x T : EuclideanSpace ℝ (Fin n)) (hx : x ∈ F)
    (hT : CubicNewton.Shared.IsCubicStep g H M x T) :
    ∀ v : EuclideanSpace ℝ (Fin n), 0 ≤ ⟪H x v, v⟫ + 1 / 2 * M * ‖x - T‖ * ‖v‖ ^ 2 := by
  intro v
  have FO := aux_chp_first_order g H M x T hT
  rw [norm_sub_rev]
  set h := T - x with hh
  set A := H x with hA
  set G := g x with hG
  have expand : ∀ (t : ℝ) (w : EuclideanSpace ℝ (Fin n)),
      CubicNewton.Shared.cubicModel g H M x (T + t • w)
        = ⟪G, h⟫ + t * ⟪G, w⟫
          + 1 / 2 * (⟪A h, h⟫ + t * ⟪A h, w⟫ + t * ⟪A w, h⟫ + t ^ 2 * ⟪A w, w⟫)
          + M / 6 * ‖h + t • w‖ ^ 3 := by
    intro t w
    have e : T + t • w - x = h + t • w := by rw [hh]; abel
    simp only [CubicNewton.Shared.cubicModel, e, map_add, map_smul, inner_add_left,
      inner_add_right, real_inner_smul_left, real_inner_smul_right]
    ring
  have hT0 : CubicNewton.Shared.cubicModel g H M x T
      = ⟪G, h⟫ + 1 / 2 * ⟪A h, h⟫ + M / 6 * ‖h‖ ^ 3 := by
    rfl
  by_cases hr0 : ‖h‖ = 0
  · have h0 : h = 0 := norm_eq_zero.mp hr0
    rw [hr0]
    have key : ∀ t : ℝ, 0 < t → 0 ≤ ⟪A v, v⟫ + M / 3 * t * ‖v‖ ^ 3 := by
      intro t ht
      have h1 := hT (T + t • v)
      rw [expand, hT0] at h1
      have FOv := FO v
      rw [h0] at FOv h1
      simp only [inner_zero_left, inner_zero_right, map_zero, norm_zero, mul_zero, add_zero,
        zero_add] at FOv h1
      rw [norm_smul, Real.norm_eq_abs, abs_of_pos ht, FOv] at h1
      have h2 : 0 ≤ t ^ 2 * (⟪A v, v⟫ + M / 3 * t * ‖v‖ ^ 3) := by nlinarith
      exact (mul_nonneg_iff_of_pos_left (by positivity)).mp h2
    have hc : Continuous (fun t : ℝ => ⟪A v, v⟫ + M / 3 * t * ‖v‖ ^ 3) := by fun_prop
    have := ge_of_tendsto ((hc.tendsto 0).mono_left nhdsWithin_le_nhds)
      (eventually_nhdsWithin_of_forall (s := Set.Ioi 0) key)
    simpa using this
  · have hrpos : 0 < ‖h‖ := lt_of_le_of_ne (norm_nonneg _) (Ne.symm hr0)
    have main : ∀ u, ⟪h, u⟫ ≠ 0 → 0 ≤ ⟪A u, u⟫ + 1 / 2 * M * ‖h‖ * ‖u‖ ^ 2 := by
      intro u hu
      have hu0 : u ≠ 0 := by rintro rfl; simp at hu
      have hN : 0 < ‖u‖ ^ 2 := by positivity
      set t := -2 * ⟪h, u⟫ / ‖u‖ ^ 2 with ht
      have htN : t * ‖u‖ ^ 2 = -2 * ⟪h, u⟫ := by rw [ht]; field_simp
      have htne : t ≠ 0 := by
        rw [ht]
        exact div_ne_zero (mul_ne_zero (by norm_num) hu) hN.ne'
      have hsph : ‖h + t • u‖ = ‖h‖ := by
        have hsq : ‖h + t • u‖ ^ 2 = ‖h‖ ^ 2 := by
          rw [norm_add_sq_real, norm_smul, real_inner_smul_right, mul_pow, Real.norm_eq_abs,
            sq_abs]
          have : t * (t * ‖u‖ ^ 2) = t * (-2 * ⟪h, u⟫) := by rw [htN]
          nlinarith
        exact (pow_left_inj₀ (norm_nonneg _) (norm_nonneg _) two_ne_zero).mp hsq
      have h1 := hT (T + t • u)
      rw [expand, hT0, hsph] at h1
      have FOu := FO u
      have e1 : t * (⟪G, u⟫ + 1 / 2 * (⟪A h, u⟫ + ⟪A u, h⟫) + M / 2 * ‖h‖ * ⟪h, u⟫) = 0 := by
        rw [FOu]; ring
      have e2 : M * ‖h‖ * (t * (t * ‖u‖ ^ 2)) = M * ‖h‖ * (t * (-2 * ⟪h, u⟫)) := by rw [htN]
      have key : 0 ≤ t ^ 2 * (⟪A u, u⟫ + 1 / 2 * M * ‖h‖ * ‖u‖ ^ 2) := by nlinarith
      exact (mul_nonneg_iff_of_pos_left (by positivity)).mp key
    by_cases hp : ⟪h, v⟫ = 0
    · have key : ∀ ε : ℝ, 0 < ε →
          0 ≤ ⟪A (v + ε • h), v + ε • h⟫ + 1 / 2 * M * ‖h‖ * ‖v + ε • h‖ ^ 2 := by
        intro ε hε
        apply main
        rw [inner_add_right, hp, real_inner_smul_right, real_inner_self_eq_norm_sq, zero_add]
        exact mul_ne_zero hε.ne' (pow_ne_zero 2 hr0)
      have hc : Continuous
          (fun ε : ℝ => ⟪A (v + ε • h), v + ε • h⟫ + 1 / 2 * M * ‖h‖ * ‖v + ε • h‖ ^ 2) := by
        fun_prop
      have := ge_of_tendsto ((hc.tendsto 0).mono_left nhdsWithin_le_nhds)
        (eventually_nhdsWithin_of_forall (s := Set.Ioi 0) key)
      simpa using this
    · exact main v hp
