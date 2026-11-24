-- Prove2me | solution 1 for Formalism.HermitianLattices.Ext.LogarithmicIntegralBounds.mainAP_lower
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-24T07:28:21.757608+00:00
-- url     : https://prove2.me/submissions/4fde26ea-d74f-4d39-9844-ec9942322a65

import Mathlib
import Definitions.Def_Formalism_GL3MeanSquares_GenusMeanAsymptotics_JacobiCharacterSums_MeanSquareHypWIff
import Definitions.Def_Formalism_LandauZeroFreeBounds_LogDerivRegionChiOf
import Definitions.Def_Formalism_GL3MeanSquares_GenusMeanAsymptotics_JacobiCharacterSums_MSqCount
import Theorems.Thm_Formalism_HermitianLattices_Ext_LogarithmicIntegralBounds_liX_sub_ge
import Theorems.Thm_Formalism_HermitianLattices_Ext_LogarithmicIntegralBounds_liX_two
import Theorems.Thm_Formalism_HermitianLattices_Ext_LogarithmicIntegralBounds_liX_nonneg
import Theorems.Thm_Formalism_HermitianLattices_Ext_LogarithmicIntegralBounds_exp_neg_le_one_sub_half

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Finset Classical
noncomputable section
open Formalism Formalism.HermitianLattices Formalism.HermitianLattices.Ext Formalism.HermitianLattices.Ext.LogarithmicIntegralBounds
open Formalism.HermitianLattices.ZeroFreeRegionGL2
namespace Formalism.HermitianLattices.Ext.LogarithmicIntegralBounds
theorem _root_.solution {M : ℕ} [NeZero M] (h8 : 8 ∣ M) (e : Option (DirichletCharacter ℂ M × ℝ))
    (he : ∀ p : DirichletCharacter ℂ M × ℝ, e = some p → IsExcPair p.1 p.2)
    (c : ℝ) (hc0 : 0 < c) (hc1 : c ≤ 1)
    (hc : ∀ (χ : DirichletCharacter ℂ M) (β : ℝ), χ ^ 2 = 1 → χ ≠ 1 →
      DirichletCharacter.LFunction χ (β : ℂ) = 0 → β ≤ 1 - c * (M : ℝ) ^ (-1 : ℝ))
    (b : ℕ) (X : ℝ) (hX : 0 < X) (hY : 4 ≤ Real.log X) :
    c * X / (2 * Real.log X * (M : ℝ) ^ 2) ≤ mainAP e b X := by
  have hM8 : (8:ℝ) ≤ M := by exact_mod_cast Nat.le_of_dvd (Nat.pos_of_ne_zero (NeZero.ne M)) h8
  have hMpos : (0:ℝ) < M := by linarith
  have hlogX : 0 < Real.log X := by linarith
  have hX5 : 5 ≤ X := by
    have h := Real.add_one_le_exp (Real.log X)
    rw [Real.exp_log hX] at h
    linarith
  have hX2 : (2:ℝ) ≤ X := by linarith
  have hlogM : 1 ≤ Real.log M := by
    have h1 : Real.log 8 ≤ Real.log M := Real.log_le_log (by norm_num) hM8
    have h2 : (1:ℝ) ≤ Real.log 8 := by
      rw [Real.le_log_iff_exp_le (by norm_num)]
      linarith [Real.exp_one_lt_d9]
    linarith
  have hcM0 : 0 ≤ c / M := div_nonneg hc0.le hMpos.le
  have hcM1 : c / M ≤ 1 := by
    rw [div_le_iff₀ hMpos]
    linarith
  have hfin : ∀ N : ℝ, c * X / (2 * Real.log X * M) ≤ N →
      c * X / (2 * Real.log X * (M:ℝ) ^ 2) ≤ N / (M.totient : ℝ) := by
    intro N hN
    have hT0 : 0 ≤ c * X / (2 * Real.log X * M) :=
      div_nonneg (mul_nonneg hc0.le hX.le) (mul_pos (mul_pos two_pos hlogX) hMpos).le
    have hN0 : 0 ≤ N := le_trans hT0 hN
    have hφpos : (0:ℝ) < M.totient := by
      exact_mod_cast Nat.totient_pos.mpr (Nat.pos_of_ne_zero (NeZero.ne M))
    have hφle : (M.totient : ℝ) ≤ M := by exact_mod_cast Nat.totient_le M
    calc c * X / (2 * Real.log X * (M:ℝ) ^ 2) = (c * X / (2 * Real.log X * M)) / M := by ring
      _ ≤ N / M := div_le_div_of_nonneg_right hN hMpos.le
      _ ≤ N / M.totient := div_le_div_of_nonneg_left hN0 hφpos hφle
  have hT : c * X / (2 * Real.log X * M) = (c * X / (2 * M)) / Real.log X := by ring
  cases e with
  | none =>
    show c * X / (2 * Real.log X * (M:ℝ) ^ 2) ≤ liX X / (M.totient : ℝ)
    apply hfin
    have h := liX_sub_ge (le_refl (2:ℝ)) hX2
    rw [liX_two, sub_zero] at h
    have hXM : c * X / (2 * M) ≤ X - 2 := by
      rw [div_le_iff₀ (by linarith)]
      nlinarith
    rw [hT]
    exact le_trans (div_le_div_of_nonneg_right hXM hlogX.le) h
  | some p =>
    obtain ⟨χ₁, β₁⟩ := p
    obtain ⟨hsq, hne1, hL0, hβlow, hβ1⟩ := he (χ₁, β₁) rfl
    have hβc := hc χ₁ β₁ hsq hne1 hL0
    rw [Real.rpow_neg_one, ← div_eq_mul_inv] at hβc
    have hβ78 : 7 / 8 ≤ β₁ := by
      have h1 : 1 / (8 * Real.log M) ≤ 1 / 8 := one_div_le_one_div_of_le (by norm_num) (by linarith)
      linarith
    have hXβ_eq : X ^ β₁ = Real.exp (Real.log X * β₁) := Real.rpow_def_of_pos hX β₁
    have hXβ2 : 2 ≤ X ^ β₁ := by
      rw [hXβ_eq]
      have := Real.add_one_le_exp (Real.log X * β₁)
      nlinarith
    have hXβX : X ^ β₁ ≤ X := by
      have := Real.rpow_le_rpow_of_exponent_le (by linarith : (1:ℝ) ≤ X) hβ1.le
      rwa [Real.rpow_one] at this
    have hXβup : X ^ β₁ ≤ X * Real.exp (-(c / M)) := by
      have hle : Real.log X * β₁ ≤ Real.log X + -(c / M) := by
        nlinarith [mul_le_mul_of_nonneg_left hβc hlogX.le, le_mul_of_one_le_left hcM0 hlogM]
      calc X ^ β₁ = Real.exp (Real.log X * β₁) := hXβ_eq
        _ ≤ Real.exp (Real.log X + -(c / M)) := Real.exp_le_exp.mpr hle
        _ = X * Real.exp (-(c / M)) := by rw [Real.exp_add, Real.exp_log hX]
    have hexp := exp_neg_le_one_sub_half hcM0 hcM1
    have hgap : c * X / (2 * M) ≤ X - X ^ β₁ := by
      have h1 : X * Real.exp (-(c / M)) ≤ X * (1 - c / M / 2) := mul_le_mul_of_nonneg_left hexp hX.le
      have e2 : c * X / (2 * M) = X * (c / M / 2) := by ring
      rw [e2]
      nlinarith
    have hθ : (χ₁ (b : ZMod M)).re ≤ 1 :=
      le_trans (Complex.re_le_norm _) (DirichletCharacter.norm_le_one χ₁ _)
    have hL0' : 0 ≤ liX (X ^ β₁) := liX_nonneg hXβ2
    have hsub := liX_sub_ge hXβ2 hXβX
    show c * X / (2 * Real.log X * (M:ℝ) ^ 2) ≤
      (liX X - (χ₁ (b : ZMod M)).re * liX (X ^ β₁)) / (M.totient : ℝ)
    apply hfin
    rw [hT]
    have h3 : (c * X / (2 * M)) / Real.log X ≤ (X - X ^ β₁) / Real.log X :=
      div_le_div_of_nonneg_right hgap hlogX.le
    nlinarith [mul_le_mul_of_nonneg_right hθ hL0']
end Formalism.HermitianLattices.Ext.LogarithmicIntegralBounds
