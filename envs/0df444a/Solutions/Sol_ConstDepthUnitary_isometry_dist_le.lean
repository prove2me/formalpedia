-- Prove2me | solution 1 for ConstDepthUnitary.isometry_dist_le
-- status  : ACCEPTED   (prove)
-- author  : @garyholm
-- created : 2026-11-17T09:30:49.862206+00:00
-- url     : https://prove2.me/submissions/c1b5cb97-26cb-4b97-8c49-64ee8a5b60e8

import Mathlib
namespace ConstDepthUnitary

theorem isometry_dist_le {H₁ H₂ : Type*}
    [NormedAddCommGroup H₁] [InnerProductSpace ℂ H₁] [CompleteSpace H₁]
    [NormedAddCommGroup H₂] [InnerProductSpace ℂ H₂] [CompleteSpace H₂]
    (V W : H₁ →ₗᵢ[ℂ] H₂) (β : ℝ) (hβ : 0 < β) :
    ‖V.toContinuousLinearMap - W.toContinuousLinearMap‖ ≤
      2 / (1 + β) * ‖V.toContinuousLinearMap - (β : ℂ) • W.toContinuousLinearMap‖ := by
  have hc : 0 ≤ 2 / (1 + β) := by positivity
  apply ContinuousLinearMap.opNorm_le_bound _ (mul_nonneg hc (norm_nonneg _))
  intro x
  have hpt : ‖V x - W x‖ ≤ 2 / (1 + β) * ‖V x - (β : ℂ) • W x‖ := by
    set r := RCLike.re (inner ℂ (V x) (W x)) with hr
    have hr1 : |r| ≤ ‖x‖ ^ 2 := by
      have h1 := RCLike.abs_re_le_norm (inner ℂ (V x) (W x))
      have h2 := norm_inner_le_norm (𝕜 := ℂ) (V x) (W x)
      rw [LinearIsometry.norm_map, LinearIsometry.norm_map] at h2
      calc |r| ≤ _ := h1
        _ ≤ _ := h2
        _ = ‖x‖ ^ 2 := by ring
    have e1 : ‖V x - W x‖ ^ 2 = 2 * ‖x‖ ^ 2 - 2 * r := by
      rw [@norm_sub_sq ℂ, LinearIsometry.norm_map, LinearIsometry.norm_map]; ring
    have e2 : ‖V x - (β : ℂ) • W x‖ ^ 2 = (1 + β ^ 2) * ‖x‖ ^ 2 - 2 * β * r := by
      rw [@norm_sub_sq ℂ, LinearIsometry.norm_map, norm_smul, LinearIsometry.norm_map,
        inner_smul_right]
      have : RCLike.re ((β : ℂ) * inner ℂ (V x) (W x)) = β * r := by
        rw [hr]; simp
      rw [this, Complex.norm_real, Real.norm_eq_abs, abs_of_pos hβ]; ring
    have hsq : ‖V x - W x‖ ^ 2 ≤ (2 / (1 + β) * ‖V x - (β : ℂ) • W x‖) ^ 2 := by
      rw [mul_pow, e1, e2, div_pow]
      have h1b : 0 < (1 + β) ^ 2 := by positivity
      rw [div_mul_eq_mul_div, le_div_iff₀ h1b]
      have hr2 : -(‖x‖ ^ 2) ≤ r := neg_le_of_abs_le hr1
      nlinarith [mul_nonneg (sq_nonneg (1 - β)) (show 0 ≤ ‖x‖ ^ 2 + r by linarith)]
    exact (pow_le_pow_iff_left₀ (norm_nonneg _) (mul_nonneg hc (norm_nonneg _)) two_ne_zero).mp hsq
  calc ‖(V.toContinuousLinearMap - W.toContinuousLinearMap) x‖ = ‖V x - W x‖ := rfl
    _ ≤ 2 / (1 + β) * ‖V x - (β : ℂ) • W x‖ := hpt
    _ = 2 / (1 + β) * ‖(V.toContinuousLinearMap - (β : ℂ) • W.toContinuousLinearMap) x‖ := rfl
    _ ≤ 2 / (1 + β) * (‖V.toContinuousLinearMap - (β : ℂ) • W.toContinuousLinearMap‖ * ‖x‖) :=
        mul_le_mul_of_nonneg_left (ContinuousLinearMap.le_opNorm _ _) hc
    _ = _ := by ring

end ConstDepthUnitary

theorem solution {H₁ H₂ : Type*}
    [NormedAddCommGroup H₁] [InnerProductSpace ℂ H₁] [CompleteSpace H₁]
    [NormedAddCommGroup H₂] [InnerProductSpace ℂ H₂] [CompleteSpace H₂]
    (V W : H₁ →ₗᵢ[ℂ] H₂) (β : ℝ) (hβ : 0 < β) :
    ‖V.toContinuousLinearMap - W.toContinuousLinearMap‖ ≤
      2 / (1 + β) * ‖V.toContinuousLinearMap - (β : ℂ) • W.toContinuousLinearMap‖ :=
  ConstDepthUnitary.isometry_dist_le V W β hβ
