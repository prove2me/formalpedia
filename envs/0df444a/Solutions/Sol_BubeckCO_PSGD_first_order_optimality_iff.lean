-- Prove2me | solution 1 for BubeckCO.PSGD.first_order_optimality_iff
-- status  : ACCEPTED   (prove)
-- author  : @kmehltretter82
-- created : 2026-11-01T22:34:26.714307+00:00
-- url     : https://prove2.me/submissions/f3671f52-13ac-4969-b27d-d0bb3751d5d0

import Mathlib
set_option autoImplicit false

open scoped Topology

theorem solution {n : ℕ} (X : Set (EuclideanSpace ℝ (Fin n)))
    (hXclosed : IsClosed X) (hXconv : Convex ℝ X)
    (f : EuclideanSpace ℝ (Fin n) → ℝ) (hfconv : ConvexOn ℝ X f)
    (hfdiff : ∀ x ∈ X, DifferentiableAt ℝ f x)
    (xstar : EuclideanSpace ℝ (Fin n)) (hxstar : xstar ∈ X) :
    IsMinOn f X xstar ↔ ∀ y ∈ X, inner ℝ (gradient f xstar) (xstar - y) ≤ 0 := by
  rw [isMinOn_iff]
  have h_grad : ∀ v, inner ℝ (gradient f xstar) v = fderiv ℝ f xstar v := fun v =>
    InnerProductSpace.toDual_symm_apply
  have h_deriv : ∀ y,
      Filter.Tendsto (fun t : ℝ => t⁻¹ * (f (xstar + t • (y - xstar)) - f xstar))
        (𝓝[>] 0) (𝓝 (fderiv ℝ f xstar (y - xstar))) := by
    intro y
    have hψ : HasDerivAt (fun t : ℝ => xstar + t • (y - xstar)) (y - xstar) 0 := by
      simpa using ((hasDerivAt_id (0 : ℝ)).smul_const (y - xstar)).const_add xstar
    have hf0 : HasFDerivAt f (fderiv ℝ f xstar) (xstar + (0 : ℝ) • (y - xstar)) := by
      simpa using (hfdiff xstar hxstar).hasFDerivAt
    have hg : HasDerivAt (fun t : ℝ => f (xstar + t • (y - xstar)))
        (fderiv ℝ f xstar (y - xstar)) 0 := hf0.comp_hasDerivAt 0 hψ
    simpa [smul_eq_mul] using hg.tendsto_slope_zero_right
  have h_Ioo : Set.Ioo (0 : ℝ) 1 ∈ 𝓝[>] (0 : ℝ) :=
    Filter.inter_mem self_mem_nhdsWithin (nhdsWithin_le_nhds (Iio_mem_nhds zero_lt_one))
  have h_seg : ∀ (y : EuclideanSpace ℝ (Fin n)) (t : ℝ),
      xstar + t • (y - xstar) = (1 - t) • xstar + t • y := fun y t => by module
  constructor
  · intro hmin y hy
    have h_ev : ∀ᶠ t : ℝ in 𝓝[>] 0,
        0 ≤ t⁻¹ * (f (xstar + t • (y - xstar)) - f xstar) := by
      filter_upwards [h_Ioo] with t ⟨ht0, ht1⟩
      have h_mem : xstar + t • (y - xstar) ∈ X := by
        rw [h_seg]
        exact hXconv hxstar hy (by linarith) ht0.le (by ring)
      have h_le : f xstar ≤ f (xstar + t • (y - xstar)) := hmin _ h_mem
      exact mul_nonneg (inv_nonneg.mpr ht0.le) (sub_nonneg.mpr h_le)
    have h_nonneg : 0 ≤ fderiv ℝ f xstar (y - xstar) :=
      ge_of_tendsto (h_deriv y) h_ev
    have h_eq : inner ℝ (gradient f xstar) (xstar - y) = -fderiv ℝ f xstar (y - xstar) := by
      rw [h_grad, ← neg_sub y xstar, ContinuousLinearMap.map_neg]
    linarith
  · intro h_opt y hy
    have h_ev : ∀ᶠ t : ℝ in 𝓝[>] 0,
        t⁻¹ * (f (xstar + t • (y - xstar)) - f xstar) ≤ f y - f xstar := by
      filter_upwards [h_Ioo] with t ⟨ht0, ht1⟩
      have h_conv_ineq : f (xstar + t • (y - xstar)) ≤ (1 - t) * f xstar + t * f y := by
        rw [h_seg]
        exact hfconv.2 hxstar hy (by linarith) ht0.le (by ring)
      have h_sub : f (xstar + t • (y - xstar)) - f xstar ≤ t * (f y - f xstar) := by
        linarith
      calc t⁻¹ * (f (xstar + t • (y - xstar)) - f xstar)
          ≤ t⁻¹ * (t * (f y - f xstar)) :=
            mul_le_mul_of_nonneg_left h_sub (inv_nonneg.mpr ht0.le)
        _ = f y - f xstar := by
            rw [← mul_assoc, inv_mul_cancel₀ ht0.ne', one_mul]
    have h_le : fderiv ℝ f xstar (y - xstar) ≤ f y - f xstar :=
      le_of_tendsto (h_deriv y) h_ev
    have h_hy := h_opt y hy
    have h_eq : inner ℝ (gradient f xstar) (xstar - y) = -fderiv ℝ f xstar (y - xstar) := by
      rw [h_grad, ← neg_sub y xstar, ContinuousLinearMap.map_neg]
    linarith
