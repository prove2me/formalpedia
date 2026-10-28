-- Prove2me | solution 1 for ErrBoundQG.ProxLin.eq_5_2
-- status  : ACCEPTED   (prove)
-- author  : @shivm
-- created : 2026-10-26T12:55:12.113589+00:00
-- url     : https://prove2.me/submissions/60ecf299-87e9-4132-8cde-f6ce6b89251d

import Mathlib
import Definitions.Def_ErrBoundQG_ProxLin_Setting

open ErrBoundQG.ProxLin in
theorem solution {n m : ℕ}
    (g : En n → EReal) (hg : RockafellarMaxMono.Shared.ProperConvex g)
    (hgc : LowerSemicontinuous g)
    (h : En m → ℝ) (hh : ConvexOn ℝ Set.univ h)
    (c : En n → En m) (hc : ContDiff ℝ 1 c)
    (L β : ℝ) (hL : 0 ≤ L) (hβ : 0 ≤ β)
    (hhL : ∀ a b, |h a - h b| ≤ L * ‖a - b‖)
    (hcβ : ∀ x y, ‖fderiv ℝ c x - fderiv ℝ c y‖ ≤ β * ‖x - y‖)
    (x y : En n) :
    -(L * β / 2) * ‖x - y‖ ^ 2 ≤
        h (c y) - h (c x + fderiv ℝ c x (y - x)) ∧
    h (c y) - h (c x + fderiv ℝ c x (y - x)) ≤
        L * β / 2 * ‖x - y‖ ^ 2 := by
  set v := y - x with hv
  set K := ‖v‖ with hK
  have hcd : Differentiable ℝ c := hc.differentiable one_ne_zero
  set φ : ℝ → En m := fun t => c (x + t • v) - t • (fderiv ℝ c x v) - c x with hφ
  have hφd : ∀ t : ℝ, HasDerivAt φ (fderiv ℝ c (x + t • v) v - fderiv ℝ c x v) t := by
    intro t
    have hpath : HasDerivAt (fun s : ℝ => x + s • v) v t := by
      have := ((hasDerivAt_id t).smul_const v).const_add x
      simpa using this
    have h1 : HasDerivAt (fun s : ℝ => c (x + s • v)) (fderiv ℝ c (x + t • v) v) t :=
      (hcd (x + t • v)).hasFDerivAt.comp_hasDerivAt t hpath
    have h2 : HasDerivAt (fun s : ℝ => s • (fderiv ℝ c x v)) (fderiv ℝ c x v) t := by
      have := (hasDerivAt_id t).smul_const (fderiv ℝ c x v)
      simpa using this
    exact (h1.sub h2).sub_const (c x)
  have hbound : ∀ t ∈ Set.Ico (0 : ℝ) 1,
      ‖fderiv ℝ c (x + t • v) v - fderiv ℝ c x v‖ ≤ β * t * K ^ 2 := by
    intro t ht
    rw [← ContinuousLinearMap.sub_apply]
    calc ‖(fderiv ℝ c (x + t • v) - fderiv ℝ c x) v‖
        ≤ ‖fderiv ℝ c (x + t • v) - fderiv ℝ c x‖ * ‖v‖ := ContinuousLinearMap.le_opNorm _ _
      _ ≤ β * ‖x + t • v - x‖ * ‖v‖ := mul_le_mul_of_nonneg_right (hcβ _ _) (norm_nonneg _)
      _ = β * t * K ^ 2 := by
        rw [add_sub_cancel_left, norm_smul, Real.norm_eq_abs, abs_of_nonneg ht.1]
        ring
  have hB : ∀ t : ℝ, HasDerivAt (fun s : ℝ => β / 2 * s ^ 2 * K ^ 2) (β * t * K ^ 2) t := by
    intro t
    have := ((hasDerivAt_pow 2 t).const_mul (β / 2)).mul_const (K ^ 2)
    refine this.congr_deriv ?_
    rw [show (2 : ℕ) - 1 = 1 from rfl, pow_one]
    push_cast
    ring
  have hφ0 : ‖φ 0‖ ≤ β / 2 * (0 : ℝ) ^ 2 * K ^ 2 := by
    simp [hφ]
  have hmain := image_norm_le_of_norm_deriv_right_le_deriv_boundary
    (f := φ) (a := 0) (b := 1)
    (fun t _ => (hφd t).continuousAt.continuousWithinAt)
    (fun t _ => (hφd t).hasDerivWithinAt) hφ0 hB hbound
    (Set.right_mem_Icc.mpr zero_le_one)
  have hφ1 : φ 1 = c y - (c x + fderiv ℝ c x (y - x)) := by
    simp only [hφ, one_smul, hv]
    rw [add_sub_cancel]
    abel
  rw [hφ1] at hmain
  have hxy : ‖x - y‖ = K := by rw [hK, hv, norm_sub_rev]
  have hlip := hhL (c y) (c x + fderiv ℝ c x (y - x))
  have hfin : |h (c y) - h (c x + fderiv ℝ c x (y - x))| ≤ L * β / 2 * ‖x - y‖ ^ 2 := by
    rw [hxy]
    calc _ ≤ L * ‖c y - (c x + fderiv ℝ c x (y - x))‖ := hlip
      _ ≤ L * (β / 2 * 1 ^ 2 * K ^ 2) := mul_le_mul_of_nonneg_left hmain hL
      _ = L * β / 2 * K ^ 2 := by ring
  constructor
  · have := neg_abs_le (h (c y) - h (c x + fderiv ℝ c x (y - x)))
    nlinarith
  · exact (le_abs_self _).trans hfin
