-- Prove2me | solution 1 for CondatPD.FB.eq_29
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-05T23:09:13.691986+00:00
-- url     : https://prove2.me/submissions/7cda46fa-0360-4a56-aaa4-c002672af4b2

import Mathlib
import Definitions.Def_CondatPD_FB_Setting

set_option autoImplicit false

open CondatPD.FB in
theorem solution {X Y : Type*} [NormedAddCommGroup X]
    [InnerProductSpace ℝ X] [CompleteSpace X] [NormedAddCommGroup Y]
    [InnerProductSpace ℝ Y] [CompleteSpace Y]
    (L : X →L[ℝ] Y) (β τ σ : ℝ)
    (hβ : 0 < β) (hτ : 0 < τ) (hσ : 0 < σ) :
    ∀ (x : X) (y : Y), β * ((1 / τ - σ * ‖L‖ ^ 2) / β) * ‖x‖ ^ 2 ≤
      qP τ σ L x y := by
  intro x y
  have hq : qP τ σ L x y = (1 / τ) * ‖x‖ ^ 2 - 2 * inner ℝ (L x) y + (1 / σ) * ‖y‖ ^ 2 := by
    unfold qP
    rw [inner_sub_right, inner_smul_right, ContinuousLinearMap.adjoint_inner_right,
      inner_add_right, inner_neg_right, inner_smul_right, real_inner_self_eq_norm_sq,
      real_inner_self_eq_norm_sq, real_inner_comm (L x) y]
    ring
  rw [hq]
  have hb : β * ((1 / τ - σ * ‖L‖ ^ 2) / β) = 1 / τ - σ * ‖L‖ ^ 2 := by
    field_simp
  rw [hb]
  have h1 : inner ℝ (L x) y ≤ ‖L‖ * ‖x‖ * ‖y‖ := by
    calc inner ℝ (L x) y ≤ ‖L x‖ * ‖y‖ := real_inner_le_norm _ _
      _ ≤ ‖L‖ * ‖x‖ * ‖y‖ := by
        gcongr
        exact L.le_opNorm x
  have h2 : 0 ≤ (σ * (‖L‖ * ‖x‖) - ‖y‖) ^ 2 := sq_nonneg _
  have h3 : 2 * (‖L‖ * ‖x‖ * ‖y‖) ≤ σ * (‖L‖ * ‖x‖) ^ 2 + (1 / σ) * ‖y‖ ^ 2 := by
    have : σ * (2 * (‖L‖ * ‖x‖ * ‖y‖)) ≤ σ * (σ * (‖L‖ * ‖x‖) ^ 2 + (1 / σ) * ‖y‖ ^ 2) := by
      have e : σ * (σ * (‖L‖ * ‖x‖) ^ 2 + (1 / σ) * ‖y‖ ^ 2)
          = (σ * (‖L‖ * ‖x‖)) ^ 2 + ‖y‖ ^ 2 := by field_simp
      rw [e]; nlinarith
    exact le_of_mul_le_mul_left this hσ
  nlinarith
