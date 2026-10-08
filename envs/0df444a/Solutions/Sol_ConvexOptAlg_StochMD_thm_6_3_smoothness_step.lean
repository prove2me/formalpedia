-- Prove2me | solution 1 for ConvexOptAlg.StochMD.thm_6_3_smoothness_step
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-06T18:16:32.66161+00:00
-- url     : https://prove2.me/submissions/24fb12bf-e5a7-4087-8a21-ac381f146adc

import Mathlib
import Definitions.Def_ConvexOptAlg_StochMD_Defs

set_option autoImplicit false

open ConvexOptAlg.StochMD in
theorem smooth_descent_aux_6645b8eb {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    (X : Set E) (hXconv : Convex ℝ X) (f : E → ℝ) (f' : E → E →L[ℝ] ℝ) (β : ℝ)
    (hsmooth : IsSmoothWRT X f f' β) (x y : E) (hx : x ∈ X) (hy : y ∈ X) :
    f y - f x ≤ f' x (y - x) + β / 2 * ‖y - x‖ ^ 2 := by
  set v := y - x with hv
  have hmaps : Set.MapsTo (fun s : ℝ => x + s • v) (Set.Icc (0:ℝ) 1) X := by
    intro t ht
    have := hXconv.add_smul_sub_mem hx hy ht
    simpa [hv] using this
  let G : ℝ → ℝ := fun t => f (x + t • v) - t * f' x v - β / 2 * t ^ 2 * ‖v‖ ^ 2
  have hline : ∀ t : ℝ, HasDerivAt (fun s : ℝ => x + s • v) v t := by
    intro t
    simpa using ((hasDerivAt_id t).smul_const v).const_add x
  have hderivF : ∀ t ∈ Set.Icc (0:ℝ) 1,
      HasDerivWithinAt (fun s => f (x + s • v)) (f' (x + t • v) v) (Set.Icc 0 1) t := by
    intro t ht
    have h1 := hsmooth.1 _ (hmaps ht)
    exact h1.comp_hasDerivWithinAt t (hline t).hasDerivWithinAt hmaps
  have hG : ∀ t ∈ Set.Icc (0:ℝ) 1, HasDerivWithinAt G
      (f' (x + t • v) v - f' x v - β * t * ‖v‖ ^ 2) (Set.Icc 0 1) t := by
    intro t ht
    have h2 : HasDerivAt (fun s : ℝ => s * f' x v) (f' x v) t := by
      simpa using (hasDerivAt_id t).mul_const (f' x v)
    have h3 : HasDerivAt (fun s : ℝ => β / 2 * s ^ 2 * ‖v‖ ^ 2) (β * t * ‖v‖ ^ 2) t := by
      have := ((hasDerivAt_pow 2 t).const_mul (β / 2)).mul_const (‖v‖ ^ 2)
      refine this.congr_deriv ?_
      rw [show (2:ℕ) - 1 = 1 from rfl, pow_one]
      push_cast
      ring
    exact ((hderivF t ht).sub h2.hasDerivWithinAt).sub h3.hasDerivWithinAt
  have hanti : AntitoneOn G (Set.Icc 0 1) := by
    apply antitoneOn_of_hasDerivWithinAt_nonpos (convex_Icc 0 1)
    · intro t ht
      exact (hG t ht).continuousWithinAt
    · intro t ht
      rw [interior_Icc] at ht ⊢
      exact (hG t (Set.Ioo_subset_Icc_self ht)).mono Set.Ioo_subset_Icc_self
    · intro t ht
      rw [interior_Icc] at ht
      have ht' := Set.Ioo_subset_Icc_self ht
      have hL := hsmooth.2 _ (hmaps ht') x hx
      have hop : ‖(f' (x + t • v) - f' x) v‖ ≤ ‖f' (x + t • v) - f' x‖ * ‖v‖ :=
        ContinuousLinearMap.le_opNorm _ _
      have hn : ‖x + t • v - x‖ = t * ‖v‖ := by
        rw [add_sub_cancel_left, norm_smul, Real.norm_eq_abs, abs_of_pos ht.1]
      rw [hn] at hL
      have h4 : f' (x + t • v) v - f' x v ≤ ‖(f' (x + t • v) - f' x) v‖ := by
        rw [ContinuousLinearMap.sub_apply, Real.norm_eq_abs]
        exact le_abs_self _
      have hv0 := norm_nonneg v
      have h5 := mul_le_mul_of_nonneg_right hL hv0
      nlinarith
  have key := hanti (Set.left_mem_Icc.2 zero_le_one) (Set.right_mem_Icc.2 zero_le_one) zero_le_one
  have e1 : x + (1:ℝ) • v = y := by simp [hv]
  have e0 : x + (0:ℝ) • v = x := by simp
  simp only [G, e1, e0] at key
  nlinarith [key]

open ConvexOptAlg.StochMD in
theorem solution {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [FiniteDimensional ℝ E]
    (X D : Set E) (hXconv : Convex ℝ X)
    (Φ : E → ℝ) (Φ' : E → E →L[ℝ] ℝ) (hΦsc : IsStronglyConvexWRT (X ∩ D) Φ Φ' 1)
    (f : E → ℝ) (f' : E → E →L[ℝ] ℝ) (β : ℝ) (hβ : 0 ≤ β) (hsmooth : IsSmoothWRT X f f' β)
    (η : ℝ) (hη : 0 < η)
    (xs xs1 : E) (hxs : xs ∈ X ∩ D) (hxs1 : xs1 ∈ X ∩ D) (g : E →L[ℝ] ℝ) :
    f xs1 - f xs ≤
      g (xs1 - xs) + η / 2 * ‖f' xs - g‖ ^ 2 + (β + 1 / η) * bregman Φ Φ' xs1 xs := by
  have hDesc := smooth_descent_aux_6645b8eb X hXconv f f' β hsmooth xs xs1 hxs.1 hxs1.1
  have hB : ‖xs1 - xs‖ ^ 2 / 2 ≤ bregman Φ Φ' xs1 xs := by
    have h := hΦsc xs hxs xs1 hxs1
    unfold bregman
    have e : Φ' xs (xs1 - xs) = - Φ' xs (xs - xs1) := by rw [← map_neg, neg_sub]
    have hn : ‖xs - xs1‖ = ‖xs1 - xs‖ := norm_sub_rev _ _
    rw [e]
    rw [hn] at h
    linarith
  have hlin : (f' xs) (xs1 - xs) = g (xs1 - xs) + (f' xs - g) (xs1 - xs) := by simp
  have hop : (f' xs - g) (xs1 - xs) ≤ ‖f' xs - g‖ * ‖xs1 - xs‖ := by
    have := ContinuousLinearMap.le_opNorm (f' xs - g) (xs1 - xs)
    rw [Real.norm_eq_abs] at this
    exact (le_abs_self _).trans this
  set a := ‖f' xs - g‖ with ha
  set b := ‖xs1 - xs‖ with hb
  have young : a * b ≤ η / 2 * a ^ 2 + 1 / (2 * η) * b ^ 2 := by
    have k : 0 ≤ (η * a - b) ^ 2 / (2 * η) := by positivity
    have k2 : (η * a - b) ^ 2 / (2 * η) = η / 2 * a ^ 2 + 1 / (2 * η) * b ^ 2 - a * b := by
      field_simp
      ring
    linarith
  have hc : 0 ≤ β + 1 / η := by positivity
  have hm := mul_le_mul_of_nonneg_left hB hc
  have k3 : (β + 1 / η) * (b ^ 2 / 2) = β / 2 * b ^ 2 + 1 / (2 * η) * b ^ 2 := by
    field_simp
  linarith
