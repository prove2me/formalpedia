-- Prove2me | solution 1 for CondatPD.FB.P_strictly_positive
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-06T03:35:19.224115+00:00
-- url     : https://prove2.me/submissions/3d017475-4e3d-43a9-bec0-c7a3af2f47be

import Mathlib
import Definitions.Def_CondatPD_FB_Setting

set_option autoImplicit false

open InnerProductSpace in
theorem bfd76259_qP_eq {X Y : Type*} [NormedAddCommGroup X]
    [InnerProductSpace ℝ X] [CompleteSpace X] [NormedAddCommGroup Y]
    [InnerProductSpace ℝ Y] [CompleteSpace Y]
    (L : X →L[ℝ] Y) (τ σ : ℝ) (x : X) (y : Y) :
    CondatPD.FB.qP τ σ L x y =
      (1 / τ) * ‖x‖ ^ 2 - 2 * ⟪L x, y⟫_ℝ + (1 / σ) * ‖y‖ ^ 2 := by
  unfold CondatPD.FB.qP
  rw [inner_sub_right, inner_smul_right, ContinuousLinearMap.adjoint_inner_right,
    inner_add_right, inner_neg_right, inner_smul_right, real_inner_self_eq_norm_sq,
    real_inner_self_eq_norm_sq, real_inner_comm (L x) y]
  ring

open CondatPD.FB InnerProductSpace in
theorem solution {X Y : Type*} [NormedAddCommGroup X]
    [InnerProductSpace ℝ X] [CompleteSpace X] [NormedAddCommGroup Y]
    [InnerProductSpace ℝ Y] [CompleteSpace Y]
    (L : X →L[ℝ] Y) (β τ σ : ℝ)
    (hβ : 0 < β) (hτ : 0 < τ) (hσ : 0 < σ)
    (hstep : β / 2 ≤ 1 / τ - σ * ‖L‖ ^ 2) :
    ∀ (x : X) (y : Y), x ≠ 0 ∨ y ≠ 0 → 0 < qP τ σ L x y := by
  intro x y hxy
  rw [bfd76259_qP_eq]
  have ha : ⟪L x, y⟫_ℝ ≤ ‖L‖ * ‖x‖ * ‖y‖ := by
    calc ⟪L x, y⟫_ℝ ≤ ‖L x‖ * ‖y‖ := real_inner_le_norm _ _
      _ ≤ ‖L‖ * ‖x‖ * ‖y‖ := by
        gcongr
        exact L.le_opNorm x
  set a := ⟪L x, y⟫_ℝ
  have hn := norm_nonneg x
  have hm := norm_nonneg y
  have hl := norm_nonneg L
  set n := ‖x‖
  set m := ‖y‖
  set l := ‖L‖
  have hs : 0 < 1 / σ := by positivity
  have hsq : σ * (1 / σ) = 1 := by field_simp
  -- key: σ l² n² - 2 l n m + m²/σ ≥ 0
  have key : 0 ≤ σ * l ^ 2 * n ^ 2 - 2 * (l * n * m) + (1 / σ) * m ^ 2 := by
    have h1 : 0 ≤ (1 / σ) * (σ * l * n - m) ^ 2 := by positivity
    have : (1 / σ) * (σ * l * n - m) ^ 2
        = (σ * (1 / σ)) * (l ^ 2 * n ^ 2 * σ) - 2 * (σ * (1 / σ)) * (l * n * m)
          + (1 / σ) * m ^ 2 := by ring
    rw [hsq] at this
    nlinarith
  by_cases hx : x = 0
  · have hy : y ≠ 0 := hxy.resolve_left (not_not.mpr hx)
    have hn0 : n = 0 := by simp [n, hx]
    have hm0 : 0 < m := norm_pos_iff.mpr hy
    have : 0 < (1 / σ) * m ^ 2 := by positivity
    rw [hn0] at ha ⊢
    nlinarith
  · have hn0 : 0 < n := norm_pos_iff.mpr hx
    have : 0 < β / 2 * n ^ 2 := by positivity
    nlinarith
