-- Prove2me | solution 1 for FluxJacobianAnnulusEllipticity
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-22T20:13:44.404132+00:00
-- url     : https://prove2.me/submissions/09af48e3-2222-4ea3-9dc5-460dcaf69948

import Definitions.Def_PHigherOrder_FluxJacobian
import Definitions.Def_PHigherOrder_FluxJacobianAnnulusEllipticity

set_option autoImplicit false

theorem _root_.solution (p : ℝ) (hp : 1 < p) (hp2 : p < 2) (a b : ℝ)
    (ha : 0 < a) (hab : a ≤ b) :
    ∀ ξ : Plane, a ≤ ‖ξ‖ → ‖ξ‖ ≤ b → ∀ w : Plane,
    (p - 1) * b ^ (p - 2) * ‖w‖ ^ 2 ≤ inner ℝ (FluxJacobian p ξ w) w
      ∧ ‖FluxJacobian p ξ w‖ ≤ a ^ (p - 2) * ‖w‖ := by
  -- The preliminaries the estimate uses, each a one-liner from the hypotheses.
  have hp1 : 0 < p - 1 := by linarith
  have hb : 0 < b := lt_of_lt_of_le ha hab
  have hbpow : 0 < b ^ (p - 2) := Real.rpow_pos_of_pos hb _
  have hiSL : ∀ x y : Plane, (innerSL ℝ x) y = inner ℝ x y := fun _ _ => rfl
  have hmono : ∀ s t : ℝ, 0 < s → s ≤ t → t ^ (p - 2) ≤ s ^ (p - 2) := fun s t hs hst =>
    Real.rpow_le_rpow_of_nonpos hs hst (by linarith)
  intro ξ ha' hb' w
  have hn : 0 < ‖ξ‖ := lt_of_lt_of_le ha ha'
  have hn2 : (0 : ℝ) < ‖ξ‖ ^ 2 := by positivity
  have ht : 0 < ‖ξ‖ ^ (p - 2) := Real.rpow_pos_of_pos hn _
  have hval : FluxJacobian p ξ w
      = ‖ξ‖ ^ (p - 2) • (w + ((p - 2) / ‖ξ‖ ^ 2 * (inner ℝ ξ w : ℝ)) • ξ) := by
    simp only [FluxJacobian, add_apply, FunLike.coe_smul,
      Pi.smul_apply, ContinuousLinearMap.smulRight_apply, ContinuousLinearMap.id_apply,
      hiSL, smul_smul]
  -- Cauchy-Schwarz, in squared form.
  have hcs : (inner ℝ ξ w : ℝ) ^ 2 ≤ ‖ξ‖ ^ 2 * ‖w‖ ^ 2 := by
    have h := abs_real_inner_le_norm ξ w
    nlinarith [h, abs_nonneg (inner ℝ ξ w : ℝ), sq_abs (inner ℝ ξ w : ℝ),
      norm_nonneg ξ, norm_nonneg w]
  constructor
  · -- Lower bound.
    rw [hval, real_inner_smul_left, inner_add_left, real_inner_self_eq_norm_sq,
      real_inner_smul_left]
    have hbr : (p - 1) * ‖w‖ ^ 2
        ≤ ‖w‖ ^ 2 + (p - 2) / ‖ξ‖ ^ 2 * (inner ℝ ξ w : ℝ) * (inner ℝ ξ w : ℝ) := by
      have hq : (inner ℝ ξ w : ℝ) * (inner ℝ ξ w : ℝ) / ‖ξ‖ ^ 2 ≤ ‖w‖ ^ 2 := by
        rw [div_le_iff₀ hn2]
        nlinarith [hcs]
      have hkey : (p - 2) / ‖ξ‖ ^ 2 * (inner ℝ ξ w : ℝ) * (inner ℝ ξ w : ℝ)
          = (p - 2) * ((inner ℝ ξ w : ℝ) * (inner ℝ ξ w : ℝ) / ‖ξ‖ ^ 2) := by
        field_simp
        try ring
      rw [hkey]
      nlinarith [hq]
    have hbrnn : 0 ≤ ‖w‖ ^ 2 + (p - 2) / ‖ξ‖ ^ 2 * (inner ℝ ξ w : ℝ) * (inner ℝ ξ w : ℝ) := by
      nlinarith [hbr, sq_nonneg ‖w‖]
    have htb : b ^ (p - 2) ≤ ‖ξ‖ ^ (p - 2) := hmono ‖ξ‖ b hn hb'
    calc (p - 1) * b ^ (p - 2) * ‖w‖ ^ 2
        = b ^ (p - 2) * ((p - 1) * ‖w‖ ^ 2) := by ring
      _ ≤ b ^ (p - 2) * (‖w‖ ^ 2 + (p - 2) / ‖ξ‖ ^ 2 * (inner ℝ ξ w : ℝ)
            * (inner ℝ ξ w : ℝ)) := mul_le_mul_of_nonneg_left hbr hbpow.le
      _ ≤ ‖ξ‖ ^ (p - 2) * (‖w‖ ^ 2 + (p - 2) / ‖ξ‖ ^ 2 * (inner ℝ ξ w : ℝ)
            * (inner ℝ ξ w : ℝ)) := mul_le_mul_of_nonneg_right htb hbrnn
  · -- Upper bound:  squaring beats the orthogonal splitting.
    have hsqle : ‖w + ((p - 2) / ‖ξ‖ ^ 2 * (inner ℝ ξ w : ℝ)) • ξ‖ ^ 2 ≤ ‖w‖ ^ 2 := by
      rw [norm_add_sq_real, real_inner_smul_right, norm_smul, Real.norm_eq_abs,
        mul_pow, sq_abs, real_inner_comm ξ w]
      have hcoef : ((p - 2) / ‖ξ‖ ^ 2 * (inner ℝ ξ w : ℝ)) ^ 2 * ‖ξ‖ ^ 2
          = (p - 2) ^ 2 * ((inner ℝ ξ w : ℝ) ^ 2 / ‖ξ‖ ^ 2) := by
        field_simp
        try ring
      have hmid : (2 : ℝ) * ((p - 2) / ‖ξ‖ ^ 2 * (inner ℝ ξ w : ℝ) * (inner ℝ ξ w : ℝ))
          = 2 * (p - 2) * ((inner ℝ ξ w : ℝ) ^ 2 / ‖ξ‖ ^ 2) := by
        field_simp
        try ring
      rw [hcoef, hmid]
      -- `2 (p-2) + (p-2)^2 = -(2-p) p < 0`, and the quotient is nonnegative.
      have hnn : 0 ≤ (inner ℝ ξ w : ℝ) ^ 2 / ‖ξ‖ ^ 2 := by positivity
      have hfac : 0 ≤ (2 - p) * p := by nlinarith
      nlinarith [mul_nonneg hfac hnn]
    have hnormle : ‖w + ((p - 2) / ‖ξ‖ ^ 2 * (inner ℝ ξ w : ℝ)) • ξ‖ ≤ ‖w‖ := by
      have h := Real.sqrt_le_sqrt hsqle
      rwa [Real.sqrt_sq (norm_nonneg _), Real.sqrt_sq (norm_nonneg _)] at h
    have hta : ‖ξ‖ ^ (p - 2) ≤ a ^ (p - 2) := hmono a ‖ξ‖ ha ha'
    rw [hval, norm_smul, Real.norm_eq_abs, abs_of_pos ht]
    calc ‖ξ‖ ^ (p - 2) * ‖w + ((p - 2) / ‖ξ‖ ^ 2 * (inner ℝ ξ w : ℝ)) • ξ‖
        ≤ ‖ξ‖ ^ (p - 2) * ‖w‖ := mul_le_mul_of_nonneg_left hnormle ht.le
      _ ≤ a ^ (p - 2) * ‖w‖ := mul_le_mul_of_nonneg_right hta (norm_nonneg w)
