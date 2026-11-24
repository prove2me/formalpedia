-- Prove2me | solution 1 for Formalism.ZF.abs_zetaPrimeSumError_le_of_large
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-24T11:56:37.111747+00:00
-- url     : https://prove2.me/submissions/3c1f6718-9d3d-4901-9766-f55108f5b892

import Definitions.Def_Formalism_ZeroFreeRegion_ZetaLogDerivativeBounds_IntegralEqIntervalIntegralAddCompl
import Definitions.Def_Formalism_ZeroFreeRegion_ZetaLogDerivativeBounds_RiemannZetaNeZeroOfMemRectangle
import Definitions.Def_Formalism_ZeroFreeRegion_ZetaLogDerivativeBounds_NormIntegralComplLe
import Definitions.Def_Formalism_ZeroFreeRegion_ZetaLogDerivativeBounds_AbsZetaPrimeSumErrorLeOfLarge
import Theorems.Thm_Formalism_ZF_exp_mul_rpow_le
import Theorems.Thm_Formalism_ZF_integral_eq_intervalIntegral_add_compl
import Theorems.Thm_Formalism_ZF_log_exp_add_two_bounds
import Theorems.Thm_Formalism_ZF_norm_integral_compl_le
import Theorems.Thm_Formalism_ZF_norm_perronIntegrand_le_horizontal
import Theorems.Thm_Formalism_ZF_norm_perronIntegrand_le_left
import Theorems.Thm_Formalism_ZF_norm_perronIntegrand_le_right
import Theorems.Thm_Formalism_ZF_norm_sub_le_of_rectangle_identity
import Theorems.Thm_Formalism_ZF_pow_three_mul_exp_le
import Theorems.Thm_Formalism_ZF_riemannZeta_ne_zero_of_mem_rectangle


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Complex MeasureTheory
noncomputable section
open Formalism Formalism.ZF
set_option maxHeartbeats 1000000
namespace Formalism.ZF
theorem _root_.solution (c₀ c₁ C₁ C₂ : ℝ) (hC₁ : 0 ≤ C₁) (hC₂ : 0 ≤ C₂)
    (hZ : ∀ s : ℂ, s ≠ 1 → 1 - c₀ / Real.log (|s.im| + 2) ≤ s.re → riemannZeta s ≠ 0)
    (hD : ∀ s : ℂ, s ≠ 1 → 1 - c₁ / Real.log (|s.im| + 2) ≤ s.re →
      ‖deriv riemannZeta s / riemannZeta s + 1 / (s - 1)‖ ≤ C₁ * Real.log (|s.im| + 2) ^ 2)
    (hR : ∀ s : ℂ, 1 < s.re → ‖deriv riemannZeta s / riemannZeta s‖ ≤ 1 / (s.re - 1) + C₂)
    (hP : Perron) (hRS : RectShift)
    (c : ℝ) (hc : 0 < c) (hc2 : c ≤ 1 / 2) (hc0 : c ≤ c₀) (hc1 : c ≤ c₁)
    (y : ℝ) (hy : 2 ≤ y) (hs8 : 8 / c ≤ Real.sqrt (Real.log y))
    (hs1 : 1 ≤ Real.sqrt (Real.log y)) :
    |Formalism.Gz y| ≤
      (2 * Real.pi * Real.exp 1 * (1 + C₂) + 4 * Real.exp 1 * (C₁ + 1) + 4 * (C₁ + 1)) *
        (6 * (8 / c) ^ 3) * y * Real.exp (-(c / 8) * Real.sqrt (Real.log y)) := by
  obtain ⟨s, hs⟩ : ∃ s, s = Real.sqrt (Real.log y) := ⟨_, rfl⟩
  rw [← hs] at hs8 hs1 ⊢
  have hy0 : 0 < y := by linarith
  have hy1 : 1 < y := by linarith
  have hlogy : 0 < Real.log y := Real.log_pos hy1
  have hℓ : Real.log y = s ^ 2 := by rw [hs, Real.sq_sqrt hlogy.le]
  have hs0 : 0 < s := by linarith
  have hs3 : 1 ≤ s ^ 3 := one_le_pow₀ hs1
  have hs23 : s ^ 2 ≤ s ^ 3 := pow_le_pow_right₀ hs1 (by norm_num)
  obtain ⟨T, hTdef⟩ : ∃ T, T = Real.exp (c * s / 4) := ⟨_, rfl⟩
  obtain ⟨hT1, hL1, hLs⟩ := log_exp_add_two_bounds c s hc hs8
  rw [← hTdef] at hT1 hL1 hLs
  have hT0 : 0 < T := by linarith
  obtain ⟨L, hLdef⟩ : ∃ L, L = Real.log (T + 2) := ⟨_, rfl⟩
  rw [← hLdef] at hL1 hLs
  have hL0 : 0 < L := by linarith
  obtain ⟨σ₀, hσ₀⟩ : ∃ σ₀ : ℝ, σ₀ = 1 + 1 / Real.log y := ⟨_, rfl⟩
  obtain ⟨σ₁, hσ₁⟩ : ∃ σ₁ : ℝ, σ₁ = 1 - c / L := ⟨_, rfl⟩
  have hinvl : 0 < 1 / Real.log y := one_div_pos.mpr hlogy
  have hinvl1 : 1 / Real.log y ≤ 1 := by
    rw [div_le_one hlogy, hℓ]
    exact one_le_pow₀ hs1
  have hσ₀1 : 1 < σ₀ := by rw [hσ₀]; linarith
  have hcL : c / L ≤ 1 / 2 := by
    rw [div_le_iff₀ hL0]
    linarith
  have hcL0 : 0 < c / L := div_pos hc hL0
  have hσ₁0 : 0 < σ₁ := by rw [hσ₁]; linarith
  have hσ₁1 : σ₁ < 1 := by rw [hσ₁]; linarith
  have hσ₁h : 1 / 2 ≤ σ₁ := by rw [hσ₁]; linarith
  have hσ01 : σ₁ ≤ σ₀ := by linarith
  obtain ⟨hint, hperron⟩ := hP y hy1.le σ₀ hσ₀1
  have hzf := riemannZeta_ne_zero_of_mem_rectangle c₀ hZ c T σ₀ hc hc0 hT0.le
  rw [← hLdef, ← hσ₁] at hzf
  have hrect := hRS y hy0 σ₁ σ₀ T hσ₁0 hσ₁1 hσ₀1 hT0 hzf
  simp only [rectInt] at hrect
  rw [integral_eq_intervalIntegral_add_compl _ hint T hT0.le] at hperron
  have halg := norm_sub_le_of_rectangle_identity _ _ _ _ _ _ _ hperron hrect
  have hcast : ((Formalism.Gz y : ℝ) : ℂ) = ((Formalism.Sz y : ℝ) : ℂ) -
      ((y : ℂ) * Real.log y - (1 + Real.eulerMascheroniConstant) * y) := by
    simp only [Formalism.Gz]
    push_cast
    ring
  have hGz : |Formalism.Gz y| = ‖((Formalism.Sz y : ℝ) : ℂ) -
      ((y : ℂ) * Real.log y - (1 + Real.eulerMascheroniConstant) * y)‖ := by
    rw [← hcast, Complex.norm_real, Real.norm_eq_abs]
  have hE := norm_integral_compl_le (fun t : ℝ => Fy y ((σ₀ : ℂ) + t * I))
    ((Real.log y + C₂) * (Real.exp 1 * y)) T
    (mul_nonneg (by linarith) (mul_nonneg (Real.exp_pos 1).le hy0.le)) hT0 (fun t ht => by
      have h := norm_perronIntegrand_le_right C₂ hR y T t hy1 hT0 ht
      rw [← hσ₀] at h
      exact h)
  have hHx : ∀ v : ℝ, |v| = T → ∀ x ∈ Set.uIoc σ₁ σ₀,
      ‖Fy y ((x : ℂ) + (v : ℂ) * I)‖ ≤ (C₁ * L ^ 2 + 1) * y ^ σ₀ / T ^ 2 := by
    intro v hv x hx
    rw [Set.uIoc_of_le hσ01] at hx
    have h := norm_perronIntegrand_le_horizontal c₁ C₁ hC₁ hD c y T x v σ₀ hc hc1 hy1.le hT1 hv
      (by rw [← hLdef, ← hσ₁]; exact hx.1.le) hx.2
    rw [← hLdef] at h
    exact h
  have ha := intervalIntegral.norm_integral_le_of_norm_le_const
    (hHx (-T) (by rw [abs_neg, abs_of_pos hT0]))
  have hb := intervalIntegral.norm_integral_le_of_norm_le_const (hHx T (abs_of_pos hT0))
  have hV := intervalIntegral.norm_integral_le_of_norm_le_const (a := -T) (b := T)
    (f := fun u : ℝ => Fy y ((σ₁ : ℂ) + u * I))
    (C := (C₁ * L ^ 2 + L / c) * y ^ σ₁ * (2 * L / c)) (fun u hu => by
      rw [Set.uIoc_of_le (by linarith)] at hu
      have h := norm_perronIntegrand_le_left c₁ C₁ hC₁ hD c y T u hc hc1 hy0 hT0.le
        (abs_le.mpr ⟨hu.1.le, hu.2⟩) (by rw [← hLdef, ← hσ₁]; exact hσ₁h)
      rw [← hLdef, ← hσ₁] at h
      exact h)
  beta_reduce at hE hV
  obtain ⟨E', hE'def⟩ : ∃ E', E' = Real.exp (-(c * s / 4)) := ⟨_, rfl⟩
  have hE'0 : 0 < E' := by rw [hE'def]; exact Real.exp_pos _
  have hTE : T * E' = 1 := by
    rw [hTdef, hE'def, ← Real.exp_add]
    simp
  have hE'T : E' = T⁻¹ := eq_inv_of_mul_eq_one_right hTE
  have hE'1 : E' ≤ 1 := by rw [hE'T]; exact inv_le_one_of_one_le₀ hT1
  have hE'2 : E' ^ 2 ≤ E' := by
    rw [sq]
    exact mul_le_of_le_one_left hE'0.le hE'1
  have hey : 0 ≤ Real.exp 1 * y := mul_nonneg (Real.exp_pos 1).le hy0.le
  have hyσ₀ : y ^ σ₀ = Real.exp 1 * y := by
    rw [hσ₀, Real.rpow_add hy0, Real.rpow_one, Real.rpow_def_of_pos hy0,
      mul_one_div_cancel hlogy.ne']
    ring
  have hlp := exp_mul_rpow_le y c L s hy0 hℓ hc hc2 hL0 hLs hs0
  rw [← hTdef, ← hσ₁, ← hE'def] at hlp
  have hpe := pow_three_mul_exp_le c s hc hs0.le
  rw [← hE'def] at hpe
  have hLs' : L ≤ s / 4 := by
    have := mul_le_mul_of_nonneg_right hc2 hs0.le
    linarith
  have hLc : L / c ≤ s / 2 := by
    rw [div_le_iff₀ hc]
    linarith
  have hLc0 : 0 ≤ L / c := div_nonneg hL0.le hc.le
  have hL2 : L ^ 2 ≤ s ^ 2 / 16 := by
    calc L ^ 2 ≤ (s / 4) ^ 2 := pow_le_pow_left₀ hL0.le hLs' 2
      _ = s ^ 2 / 16 := by ring
  have hL3 : L ^ 2 ≤ s ^ 3 := by linarith [sq_nonneg s]
  have hlogC : Real.log y + C₂ ≤ (1 + C₂) * s ^ 3 := by
    rw [hℓ]
    calc s ^ 2 + C₂ ≤ s ^ 3 + C₂ * s ^ 3 := add_le_add hs23 (le_mul_of_one_le_right hC₂ hs3)
      _ = _ := by ring
  have hB1 : ‖∫ t in (Set.Ioc (-T) T)ᶜ, Fy y ((σ₀ : ℂ) + t * I)‖ ≤
      2 * Real.pi * ((1 + C₂) * s ^ 3 * (Real.exp 1 * y) * E') := by
    calc _ ≤ 2 * Real.pi * ((Real.log y + C₂) * (Real.exp 1 * y)) / T := hE
      _ = 2 * Real.pi * ((Real.log y + C₂) * (Real.exp 1 * y) * E') := by rw [hE'T]; ring
      _ ≤ _ := by
        apply mul_le_mul_of_nonneg_left _ (by positivity)
        apply mul_le_mul_of_nonneg_right _ hE'0.le
        exact mul_le_mul_of_nonneg_right hlogC hey
  have hA1 : C₁ * L ^ 2 + 1 ≤ (C₁ + 1) * s ^ 3 := by
    calc C₁ * L ^ 2 + 1 ≤ C₁ * s ^ 3 + s ^ 3 := add_le_add (mul_le_mul_of_nonneg_left hL3 hC₁) hs3
      _ = _ := by ring
  have hd : |σ₀ - σ₁| ≤ 2 := by
    rw [abs_of_nonneg (by linarith)]
    rw [hσ₀, hσ₁]
    linarith
  have hHb : (C₁ * L ^ 2 + 1) * y ^ σ₀ / T ^ 2 * |σ₀ - σ₁| ≤
      (C₁ + 1) * s ^ 3 * (Real.exp 1 * y) * E' * 2 := by
    rw [show (C₁ * L ^ 2 + 1) * y ^ σ₀ / T ^ 2 = (C₁ * L ^ 2 + 1) * (Real.exp 1 * y) * E' ^ 2 by
      rw [hyσ₀, hE'T]; ring]
    have hX0 : 0 ≤ (C₁ + 1) * s ^ 3 * (Real.exp 1 * y) :=
      mul_nonneg (mul_nonneg (by linarith) (pow_nonneg hs0.le 3)) hey
    exact mul_le_mul (mul_le_mul (mul_le_mul_of_nonneg_right hA1 hey) hE'2 (sq_nonneg _) hX0) hd
      (abs_nonneg _) (mul_nonneg hX0 hE'0.le)
  have hq1 : L ^ 2 * (L / c) ≤ s ^ 3 := by
    calc L ^ 2 * (L / c) ≤ s ^ 2 / 16 * (s / 2) := mul_le_mul hL2 hLc hLc0 (by positivity)
      _ = s ^ 3 / 32 := by ring
      _ ≤ s ^ 3 := by linarith
  have hq2 : (L / c) ^ 2 ≤ s ^ 3 := by
    calc (L / c) ^ 2 ≤ (s / 2) ^ 2 := pow_le_pow_left₀ hLc0 hLc 2
      _ = s ^ 2 / 4 := by ring
      _ ≤ s ^ 2 := by linarith [sq_nonneg s]
      _ ≤ s ^ 3 := hs23
  have hq : (C₁ * L ^ 2 + L / c) * (L / c) ≤ (C₁ + 1) * s ^ 3 := by
    calc (C₁ * L ^ 2 + L / c) * (L / c) = C₁ * (L ^ 2 * (L / c)) + (L / c) ^ 2 := by ring
      _ ≤ C₁ * s ^ 3 + s ^ 3 := add_le_add (mul_le_mul_of_nonneg_left hq1 hC₁) hq2
      _ = _ := by ring
  have hCb : (C₁ * L ^ 2 + L / c) * y ^ σ₁ * (2 * L / c) * |T - -T| ≤
      4 * ((C₁ + 1) * s ^ 3) * (y * E') := by
    rw [show |T - -T| = 2 * T by rw [sub_neg_eq_add, abs_of_pos (by linarith)]; ring]
    calc (C₁ * L ^ 2 + L / c) * y ^ σ₁ * (2 * L / c) * (2 * T)
        = 4 * ((C₁ * L ^ 2 + L / c) * (L / c)) * (T * y ^ σ₁) := by ring
      _ ≤ 4 * ((C₁ + 1) * s ^ 3) * (y * E') :=
        mul_le_mul (by linarith [hq]) hlp (mul_nonneg hT0.le (Real.rpow_nonneg hy0.le _))
          (mul_nonneg (by norm_num) (mul_nonneg (by linarith) (pow_nonneg hs0.le 3)))
  have hG0 : 0 ≤ ‖((Formalism.Sz y : ℝ) : ℂ) -
      ((y : ℂ) * Real.log y - (1 + Real.eulerMascheroniConstant) * y)‖ := norm_nonneg _
  have hpi : 1 ≤ 2 * Real.pi := by linarith [Real.pi_gt_three]
  have hK0 : 0 ≤ (2 * Real.pi * Real.exp 1 * (1 + C₂) + 4 * Real.exp 1 * (C₁ + 1) + 4 * (C₁ + 1)) * y := by
    apply mul_nonneg _ hy0.le
    have h1 : 0 ≤ 2 * Real.pi * Real.exp 1 * (1 + C₂) := mul_nonneg (by positivity) (by linarith)
    have h2 : 0 ≤ 4 * Real.exp 1 * (C₁ + 1) := mul_nonneg (by positivity) (by linarith)
    linarith
  rw [hGz]
  have hsum : ‖((Formalism.Sz y : ℝ) : ℂ) -
      ((y : ℂ) * Real.log y - (1 + Real.eulerMascheroniConstant) * y)‖ ≤
      (2 * Real.pi * Real.exp 1 * (1 + C₂) + 4 * Real.exp 1 * (C₁ + 1) + 4 * (C₁ + 1)) * y *
        (s ^ 3 * E') := by
    calc _ ≤ 2 * Real.pi * ‖((Formalism.Sz y : ℝ) : ℂ) -
      ((y : ℂ) * Real.log y - (1 + Real.eulerMascheroniConstant) * y)‖ := le_mul_of_one_le_left hG0 hpi
      _ ≤ _ := halg
      _ ≤ 2 * Real.pi * ((1 + C₂) * s ^ 3 * (Real.exp 1 * y) * E') +
            (C₁ + 1) * s ^ 3 * (Real.exp 1 * y) * E' * 2 +
            (C₁ + 1) * s ^ 3 * (Real.exp 1 * y) * E' * 2 + 4 * ((C₁ + 1) * s ^ 3) * (y * E') :=
          add_le_add (add_le_add (add_le_add hB1 (ha.trans hHb)) (hb.trans hHb)) (hV.trans hCb)
      _ = _ := by ring
  calc _ ≤ _ := hsum
    _ ≤ (2 * Real.pi * Real.exp 1 * (1 + C₂) + 4 * Real.exp 1 * (C₁ + 1) + 4 * (C₁ + 1)) * y *
        (6 * (8 / c) ^ 3 * Real.exp (-(c / 8) * s)) := mul_le_mul_of_nonneg_left hpe hK0
    _ = _ := by ring
end Formalism.ZF
