-- Prove2me | solution 1 for Formalism.HermitianLattices.Ext.LogarithmicIntegralBounds.count_pos
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-24T07:46:39.324236+00:00
-- url     : https://prove2.me/submissions/72dfe868-df8b-40d9-8511-44ccd5a3124b

import Mathlib
import Definitions.Def_Formalism_GL3MeanSquares_GenusMeanAsymptotics_JacobiCharacterSums_MeanSquareHypWIff
import Definitions.Def_Formalism_LandauZeroFreeBounds_LogDerivRegionChiOf
import Definitions.Def_Formalism_GL3MeanSquares_GenusMeanAsymptotics_JacobiCharacterSums_MSqCount
import Theorems.Thm_Formalism_HermitianLattices_Ext_LogarithmicIntegralBounds_piAP_le_card_PPset_add
import Theorems.Thm_Formalism_HermitianLattices_Ext_LogarithmicIntegralBounds_mainAP_lower
import Theorems.Thm_Formalism_HermitianLattices_Ext_LogarithmicIntegralBounds_size_ineq
import Theorems.Thm_Formalism_HermitianLattices_Ext_LogarithmicIntegralBounds_err_le_half
import Theorems.Thm_Formalism_HermitianLattices_Ext_LogarithmicIntegralBounds_range_ok

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
theorem _root_.solution {c₃ A₀ C₀ c ε : ℝ} (hc₃ : 0 < c₃) (hcpos : 0 < c) (hc1 : c ≤ 1) (hε : 0 < ε)
    {m₀ : ℕ} [NeZero m₀] (h8 : 8 ∣ m₀) (a₀ : ℕ) (hcop : a₀.Coprime m₀)
    (e : Option (DirichletCharacter ℂ m₀ × ℝ))
    (he1 : ∀ p : DirichletCharacter ℂ m₀ × ℝ, e = some p → IsExcPair p.1 p.2)
    (he3 : ∀ (X : ℝ) (b : ℕ), 2 ≤ X → C₀ * Real.log m₀ * Real.log (Real.log m₀ + 2) ≤ Real.log X →
      b.Coprime m₀ → |(piAP X m₀ b : ℝ) - mainAP e b X| ≤
        A₀ * (Real.exp (-(c₃ * Real.log X / Real.log m₀)) + Real.exp (-Real.sqrt (c₃ * Real.log X))) *
          mainAP e b X)
    (hcb : ∀ (χ : DirichletCharacter ℂ m₀) (β : ℝ), χ ^ 2 = 1 → χ ≠ 1 →
      DirichletCharacter.LFunction χ (β : ℂ) = 0 → β ≤ 1 - c * (m₀ : ℝ) ^ (-1 : ℝ))
    (x X : ℝ) (hx1 : 1 ≤ x) (hl320 : 320 ≤ Real.log x)
    (hlC : 4 * |C₀| * (5 + ε / 5) ≤ Real.log x)
    (hlK1 : 4 * Real.log (4 * (|A₀| + 1)) / c₃ ≤ Real.log x)
    (hlK2 : 4 * Real.log (4 * (|A₀| + 1)) ^ 2 / c₃ ≤ Real.log x)
    (hlc : |Real.log (320 / c)| ≤ Real.log x)
    (h1 : (1 / 4) * Real.log x ^ 2 * Real.log m₀ ≤ Real.log X)
    (h3 : Real.log X ≤ x ^ (ε / 5) * Real.log x ^ 2) (hpos : 0 < X) :
    X ^ (9 / 10 : ℝ) ≤ ((PPset m₀ a₀ X).card : ℝ) := by
  have hm8 : (8:ℝ) ≤ m₀ := by exact_mod_cast Nat.le_of_dvd (Nat.pos_of_ne_zero (NeZero.ne m₀)) h8
  have hmpos : (0:ℝ) < m₀ := by linarith
  have hΛ1 : 1 ≤ Real.log m₀ := by
    have h1' : Real.log 8 ≤ Real.log m₀ := Real.log_le_log (by norm_num) hm8
    have h2' : (1:ℝ) ≤ Real.log 8 := by
      rw [Real.le_log_iff_exp_le (by norm_num)]
      linarith [Real.exp_one_lt_d9]
    linarith
  have hl1 : 1 ≤ Real.log x := by linarith
  have hl2 : 320 * Real.log x ≤ Real.log x ^ 2 := by nlinarith
  have hYl : Real.log x ^ 2 / 4 ≤ Real.log X := by nlinarith
  have hY80 : 80 * Real.log m₀ ≤ Real.log X := by
    nlinarith [mul_nonneg (by linarith : (0:ℝ) ≤ Real.log m₀) (by nlinarith : (0:ℝ) ≤ Real.log x ^ 2 / 4 - 80)]
  have hY4 : 4 ≤ Real.log X := by linarith
  have hY0 : 0 < Real.log X := by linarith
  have hX2 : 2 ≤ X := by
    have h := Real.add_one_le_exp (Real.log X)
    rw [Real.exp_log hpos] at h
    linarith
  have hX1 : 1 ≤ X := by linarith
  have hrange : C₀ * Real.log m₀ * Real.log (Real.log m₀ + 2) ≤ Real.log X :=
    range_ok hε hx1 hΛ1 hl1 hlC h1 h3
  have hmain := he3 X a₀ hX2 hrange hcop
  have hll : Real.log x ≤ Real.log x ^ 2 := by nlinarith
  have hK1 : Real.log (4 * (|A₀| + 1)) ≤ c₃ * (Real.log x ^ 2 / 4) := by
    rw [div_le_iff₀ hc₃] at hlK1
    nlinarith [mul_le_mul_of_nonneg_left hll hc₃.le]
  have hK2 : Real.log (4 * (|A₀| + 1)) ^ 2 ≤ c₃ * (Real.log x ^ 2 / 4) := by
    rw [div_le_iff₀ hc₃] at hlK2
    nlinarith [mul_le_mul_of_nonneg_left hll hc₃.le]
  have herr := err_le_half (A := A₀) hc₃ (by linarith : 0 < Real.log m₀)
    (by linarith : Real.log x ^ 2 / 4 * Real.log m₀ ≤ Real.log X) hYl hK1 hK2
  have hlow := mainAP_lower h8 e he1 c hcpos hc1 hcb a₀ X hpos hY4
  have hlogc : Real.log (320 / c) ≤ Real.log X / 20 := by
    have := le_abs_self (Real.log (320 / c))
    linarith
  have hsize := size_ineq hcpos hY0 hY80 hlogc
  rw [Real.exp_log hpos, Real.exp_log hmpos] at hsize
  have hXpow : X ^ (9 / 10 : ℝ) = Real.exp (Real.log X * (9 / 10)) := Real.rpow_def_of_pos hpos _
  have hhalf : X ^ (1 / 2 : ℝ) ≤ X ^ (9 / 10 : ℝ) :=
    Real.rpow_le_rpow_of_exponent_le hX1 (by norm_num)
  have hpp := piAP_le_card_PPset_add X m₀ a₀ hX1
  set Mn := mainAP e a₀ X with hMn
  set E := Real.exp (-(c₃ * Real.log X / Real.log m₀)) + Real.exp (-Real.sqrt (c₃ * Real.log X)) with hE
  have hE0 : 0 ≤ E := by positivity
  have h4 : 0 ≤ 4 * Real.exp (Real.log X * (9 / 10)) := by positivity
  have hMn0 : 0 ≤ Mn := le_trans (le_trans h4 hsize) hlow
  have hAE : A₀ * E * Mn ≤ |A₀| * E * Mn :=
    mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right (le_abs_self A₀) hE0) hMn0
  have herr2 : |A₀| * E * Mn ≤ 1 / 2 * Mn := mul_le_mul_of_nonneg_right herr hMn0
  have habs := neg_abs_le ((piAP X m₀ a₀ : ℝ) - Mn)
  linarith
end Formalism.HermitianLattices.Ext.LogarithmicIntegralBounds
