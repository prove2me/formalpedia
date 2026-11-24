-- Prove2me | solution 1 for Formalism.ZeroFreeDirichlet.twoRealCharNoCommonZeroOfBounds
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-24T11:59:08.947472+00:00
-- url     : https://prove2.me/submissions/4ebe0765-9537-4ab0-9823-222fc49543da

import Definitions.Def_Formalism_LandauZeroFreeBounds_NoZeroComplexOf
import Definitions.Def_Formalism_LandauZeroFreeBounds_ExceptionalZeroBounds_TwoRealOf
import Theorems.Thm_Formalism_ZeroFreeDirichlet_sum_re_one_div_sub_zero_nonneg
import Theorems.Thm_Formalism_ZeroFreeDirichlet_re_negLogDeriv_le_of_real_zero

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Complex
noncomputable section
open Formalism Formalism.ZeroFreeDirichlet
namespace Formalism.ZeroFreeDirichlet
theorem _root_.solution : TwoRealOf := by
  intro hZS hLD hPos
  obtain ⟨C, hC⟩ := hZS
  obtain ⟨C', hC'0, hC'⟩ := hLD
  obtain ⟨A, hA⟩ : ∃ A : ℝ, A = 3 * |C| + 2 * C' + 1 := ⟨_, rfl⟩
  have hA1 : 1 ≤ A := by have := abs_nonneg C; linarith
  have hA0 : 0 < A := by linarith
  refine ⟨1 / (20 * A), one_div_pos.mpr (mul_pos (by norm_num) hA0), ?_⟩
  intro q hq0 χ₁ χ₂ h₁ h₂ h₁1 h₂1 h12 β₁ β₂ hr₁ hr₂
  by_contra hcon
  obtain ⟨hz₁', hz₂'⟩ := not_or.mp hcon
  have hz₁ := not_not.mp hz₁'
  have hz₂ := not_not.mp hz₂'
  obtain ⟨L, hL⟩ : ∃ L : ℝ, L = Real.log ((q : ℝ) * 2) := ⟨_, rfl⟩
  have hq : (1 : ℝ) ≤ q := by exact_mod_cast Nat.one_le_iff_ne_zero.mpr (NeZero.ne q)
  have hL2 : Real.log 2 ≤ L := by
    rw [hL]; exact Real.log_le_log (by norm_num) (by linarith)
  have hLhalf : 1 / 2 < L := by have := Real.log_two_gt_d9; linarith
  have hL0 : 0 < L := by linarith
  have hAL0 : 0 < 20 * A * L := mul_pos (mul_pos (by norm_num) hA0) hL0
  obtain ⟨e, he⟩ : ∃ e : ℝ, e = 1 / (20 * A * L) := ⟨_, rfl⟩
  have he0 : 0 < e := by rw [he]; exact one_div_pos.mpr hAL0
  have hE : 20 * A * L * e = 1 := by rw [he]; exact mul_one_div_cancel hAL0.ne'
  have hAL : A * L = 3 * |C| * L + 2 * C' * L + L := by rw [hA]; ring
  have hAL10 : 10 ≤ 20 * A * L := by nlinarith
  have he10 : e ≤ 1 / 10 := by
    have := mul_le_mul_of_nonneg_left hAL10 he0.le
    linarith
  have hreg : ∀ β : ℝ, InRegion (1 / (20 * A)) q (β : ℂ) → 1 - e ≤ β := by
    intro β hr
    simp only [InRegion, Complex.ofReal_im, Complex.ofReal_re, abs_zero, zero_add] at hr
    have : 1 / (20 * A) / Real.log ((q : ℝ) * 2) = e := by rw [he, hL, div_div]
    linarith
  have hσ : (1 : ℝ) < 1 + 2 * e := by linarith
  have hσ6 : 1 + 2 * e ≤ 6 / 5 := by linarith
  have hβlt : ∀ χ : DirichletCharacter ℂ q, χ ≠ 1 → ∀ β : ℝ,
      DirichletCharacter.LFunction χ (β : ℂ) = 0 → β < 1 := by
    intro χ hχ β hz
    by_contra h
    exact DirichletCharacter.LFunction_ne_zero_of_one_le_re χ (Or.inl hχ) (by simpa using not_lt.mp h) hz
  have hbound : ∀ χ : DirichletCharacter ℂ q, χ ≠ 1 → ∀ β : ℝ,
      InRegion (1 / (20 * A)) q (β : ℂ) → DirichletCharacter.LFunction χ (β : ℂ) = 0 →
      (negLD χ ((1 + 2 * e : ℝ) : ℂ)).re ≤ C * L - 20 * A * L / 3 := by
    intro χ hχ β hr hz
    have hb1 := hβlt χ hχ β hz
    have hb0 := hreg β hr
    obtain ⟨Z, m, hZ, hm, -, hb⟩ := hC q χ hχ 0
    have key := re_negLogDeriv_le_of_real_zero C χ hχ Z m hZ hm β (1 + 2 * e) hσ
      (by linarith) (by linarith) hb1 hz (hb (1 + 2 * e) hσ hσ6)
    rw [← hL] at key
    have h3 : 1 / (3 * e) = 20 * A * L / 3 := by
      rw [div_eq_iff (mul_pos (by norm_num) he0).ne']
      linear_combination -hE
    have hinv : 1 / (3 * e) ≤ 1 / (1 + 2 * e - β) :=
      one_div_le_one_div_of_le (by linarith) (by linarith)
    linarith
  have h0b : (negLD (1 : DirichletCharacter ℂ q) ((1 + 2 * e : ℝ) : ℂ)).re ≤ 10 * A * L + C' := by
    have h := hC' q 1 ((1 + 2 * e : ℝ) : ℂ) (by rw [Complex.ofReal_re]; exact hσ)
    rw [Complex.ofReal_re] at h
    have h2 : 1 / (1 + 2 * e - 1) = 10 * A * L := by
      rw [div_eq_iff (show (0 : ℝ) < 1 + 2 * e - 1 by linarith).ne']
      linear_combination -hE
    rw [h2] at h
    have := Complex.re_le_norm (negLD (1 : DirichletCharacter ℂ q) ((1 + 2 * e : ℝ) : ℂ))
    linarith
  have h12ne : χ₁ * χ₂ ≠ 1 := by
    intro h
    apply h12
    calc χ₁ = χ₁ * χ₂ ^ 2 := by rw [h₂, mul_one]
      _ = χ₁ * χ₂ * χ₂ := by rw [pow_two, mul_assoc]
      _ = χ₂ := by rw [h, one_mul]
  have h12b : (negLD (χ₁ * χ₂) ((1 + 2 * e : ℝ) : ℂ)).re ≤ C * L := by
    obtain ⟨Z, m, hZ, -, -, hb⟩ := hC q (χ₁ * χ₂) h12ne 0
    have hb' := hb (1 + 2 * e) hσ hσ6
    have hs := sum_re_one_div_sub_zero_nonneg (χ₁ * χ₂) h12ne Z m
      (fun ρ hρ => ((hZ ρ).1 hρ).2) (1 + 2 * e) hσ
    have hs0 : (((1 + 2 * e : ℝ) : ℂ) + ((0 : ℝ) : ℂ) * I) = ((1 + 2 * e : ℝ) : ℂ) := by simp
    have hl : (negLD (χ₁ * χ₂) (((1 + 2 * e : ℝ) : ℂ) + ((0 : ℝ) : ℂ) * I)).re =
        (negLD (χ₁ * χ₂) ((1 + 2 * e : ℝ) : ℂ)).re := by rw [hs0]
    have h02 : |(0 : ℝ)| + 2 = 2 := by norm_num
    rw [h02, ← hL] at hb'
    linarith
  have hpos := (hPos q (1 + 2 * e) hσ).2.2 χ₁ χ₂ h₁ h₂
  have k1 := hbound χ₁ h₁1 β₁ hr₁ hz₁
  have k2 := hbound χ₂ h₂1 β₂ hr₂ hz₂
  have hCL : C * L ≤ |C| * L := mul_le_mul_of_nonneg_right (le_abs_self C) hL0.le
  have hC'L : C' * (1 / 2) ≤ C' * L := mul_le_mul_of_nonneg_left hLhalf.le hC'0
  have hCL0 : 0 ≤ |C| * L := mul_nonneg (abs_nonneg C) hL0.le
  have hC'L0 : 0 ≤ C' * L := mul_nonneg hC'0 hL0.le
  linarith
end Formalism.ZeroFreeDirichlet
