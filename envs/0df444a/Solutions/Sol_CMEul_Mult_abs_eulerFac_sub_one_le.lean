-- Prove2me | solution 1 for CMEul.Mult.abs_eulerFac_sub_one_le
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T09:32:24.773826+00:00
-- url     : https://prove2.me/submissions/7c5f3ebd-74a7-4512-a7e9-c0839c2809a8

import Mathlib
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_CMEulerProducts_StepRegroup
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_CMEulerProducts_EulerFactorsMultipliable
import Theorems.Thm_CMEul_Mult_two_le_absNorm
import Theorems.Thm_CMEul_Mult_rpow_le_half

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open NumberField
noncomputable section
open CMEul CMEul.Mult
open Formalism.HermitianLatticesTheory
namespace CMEul.Mult
theorem _root_.solution {K : Type} [Field K] [NumberField K] [StarRing K] (M : ℕ)
    (hM : 3 ≤ M) (P : Ideal (𝓞 K)) (hP : P.IsMaximal) :
    |eulerFac K M P - 1| ≤ 2 * ((Ideal.absNorm P : ℕ) : ℝ) ^ (-(3 / 2 : ℝ)) := by
  have hN : (2 : ℝ) ≤ ((Ideal.absNorm P : ℕ) : ℝ) := by exact_mod_cast two_le_absNorm P hP
  set x : ℝ := ((Ideal.absNorm P : ℕ) : ℝ) with hx
  have hx0 : 0 < x := by linarith
  have hMz : -(M : ℤ) ≤ -3 := by omega
  have hhalf := rpow_le_half hN
  unfold eulerFac
  split_ifs with h
  ·
    set a : ℝ := (-1 : ℝ) ^ M * Real.sqrt x ^ (-(M : ℤ)) with ha
    have hsq1 : 1 ≤ Real.sqrt x := by
      rw [Real.one_le_sqrt]
      linarith
    have e : Real.sqrt x ^ (-3 : ℤ) = x ^ (-(3 / 2 : ℝ)) := by
      rw [Real.sqrt_eq_rpow, ← Real.rpow_intCast, ← Real.rpow_mul hx0.le]
      norm_num
    have hab : |a| ≤ x ^ (-(3 / 2 : ℝ)) := by
      rw [ha, abs_mul, abs_pow, abs_neg, abs_one, one_pow, one_mul,
        abs_of_pos (zpow_pos (by linarith) _), ← e]
      exact zpow_le_zpow_right₀ hsq1 hMz
    have hale : a ≤ 1 / 2 := le_trans (le_abs_self a) (hab.trans hhalf)
    have hne : 1 - a ≠ 0 := by linarith
    have heq : (1 - a)⁻¹ - 1 = a / (1 - a) := by
      field_simp
      ring
    rw [heq, abs_div, abs_of_pos (by linarith : (0 : ℝ) < 1 - a), div_le_iff₀ (by linarith)]
    have h0 : 0 ≤ |a| := abs_nonneg a
    nlinarith [le_abs_self a, neg_abs_le a]
  ·
    set b : ℝ := x ^ (-(M : ℤ)) with hb
    have hb0 : 0 < b := zpow_pos hx0 _
    have hb3 : b ≤ x ^ (-(3 / 2 : ℝ)) := by
      have h1 : b ≤ x ^ (-3 : ℤ) := zpow_le_zpow_right₀ (by linarith) hMz
      have h2 : x ^ (-3 : ℤ) = x ^ (-3 : ℝ) := by
        rw [← Real.rpow_intCast]
        norm_num
      have h3 : x ^ (-3 : ℝ) ≤ x ^ (-(3 / 2 : ℝ)) :=
        Real.rpow_le_rpow_of_exponent_le (by linarith) (by norm_num)
      linarith
    have hbh : b ≤ 1 / 2 := hb3.trans hhalf
    have hpos : 0 < 1 - b := by linarith
    have hle1 : 1 - b ≤ 1 := by linarith
    have hlo : 1 ≤ (1 - b) ^ (-(1 : ℝ) / 2) :=
      Real.one_le_rpow_of_pos_of_le_one_of_nonpos hpos hle1 (by norm_num)
    have hup1 : (1 - b) ^ (-(1 : ℝ) / 2) ≤ (1 - b) ^ (-1 : ℝ) :=
      Real.rpow_le_rpow_of_exponent_ge hpos hle1 (by norm_num)
    rw [Real.rpow_neg_one] at hup1
    have hup2 : (1 - b)⁻¹ ≤ 1 + 2 * b := by
      rw [inv_eq_one_div, div_le_iff₀ hpos]
      nlinarith
    rw [abs_of_nonneg (by linarith)]
    linarith
end CMEul.Mult
