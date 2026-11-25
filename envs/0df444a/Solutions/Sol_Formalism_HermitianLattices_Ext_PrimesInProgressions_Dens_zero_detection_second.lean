-- Prove2me | solution 1 for Formalism.HermitianLattices.Ext.PrimesInProgressions.Dens.zero_detection_second
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-25T07:42:03.772603+00:00
-- url     : https://prove2.me/submissions/79ccaf57-160b-4770-bf92-e01be6836b58

import Definitions.Def_Formalism_GL3MeanSquares_GenusMeanAsymptotics_JacobiCharacterSums_PNTDensSt
import Definitions.Def_Formalism_GL3MeanSquares_GenusMeanAsymptotics_JacobiCharacterSums_CountZMoll
import Definitions.Def_Formalism_GL3MeanSquares_GenusMeanAsymptotics_JacobiCharacterSums_CountZDetect
import Definitions.Def_Formalism_LFunctionBounds_LFunctionBoundsProofs_LPartialSum
import Definitions.Def_Formalism_LandauZeroFreeBounds_ExceptionalZeroBounds_LGrowth
import Definitions.Def_Formalism_GL3MeanSquares_GenusMeanAsymptotics_JacobiCharacterSums_ZeroDetectionSecond
import Theorems.Thm_Formalism_FX_l_function_partial_sum
import Theorems.Thm_Formalism_HermitianLattices_Ext_PrimitiveCharacterCasts_ZD_mollM_norm_le
import Theorems.Thm_Formalism_HermitianLattices_Ext_PrimitiveCharacterCasts_ZD_mollifier_identity
import Theorems.Thm_Formalism_HermitianLattices_Ext_PrimitiveCharacterCasts_ZD_sum_blocks
import Theorems.Thm_Formalism_ZeroFreeDirichlet_norm_character_sum_Icc_le


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Complex Finset
noncomputable section
open Formalism Formalism.HermitianLattices Formalism.HermitianLattices.Ext Formalism.HermitianLattices.Ext.PrimesInProgressions Formalism.HermitianLattices.Ext.PrimesInProgressions.Dens
open Formalism.HermitianLattices.Ext.PrimitiveCharacterCasts.ZD Formalism.ZeroFreeDirichlet
attribute [local irreducible] qd pYd pJd pNd
namespace Formalism.HermitianLattices.Ext.PrimesInProgressions.Dens
theorem _root_.solution : Detect1 := by
  intro M _ χ hχ1 T hT hM ρ hρ hρim hL
  obtain ⟨X, hX⟩ : ∃ X : ℕ, qd M T = X := ⟨_, rfl⟩
  have hMT : (M : ℝ) * T ≤ X := by rw [← hX]; unfold qd; exact Nat.le_ceil _
  have hM3 : (3 : ℝ) ≤ M := by exact_mod_cast hM
  have hX6 : (6 : ℝ) ≤ X := by nlinarith
  have hX1 : 1 ≤ X := by exact_mod_cast (show (1 : ℝ) ≤ X by linarith)
  have hre0 : 0 < ρ.re := by linarith
  have hNX : X ^ 8 ≤ pNd M T := by
    have h := Nat.lt_pow_succ_log_self (by norm_num : 1 < 2) X
    unfold pNd pJd
    rw [hX, mul_comm 8, pow_mul]
    exact Nat.pow_le_pow_left h.le 8
  have hY : pYd M T = X ^ 3 := by unfold pYd; rw [hX]
  have hYN : pYd M T ≤ pNd M T := by
    rw [hY]; exact le_trans (Nat.pow_le_pow_right hX1 (by norm_num)) hNX
  have hY1 : 1 ≤ pYd M T := by rw [hY]; exact Nat.one_le_pow _ _ (by omega)
  have hN1 : 1 ≤ pNd M T := le_trans hY1 hYN
  have hB := Formalism.ZeroFreeDirichlet.norm_character_sum_Icc_le χ hχ1
  have hP := Formalism.FX.l_function_partial_sum M χ hχ1 _ hB ρ hre0 (pNd M T) hN1
  rw [hL, zero_sub, norm_neg] at hP
  have hMI := mollifier_identity M χ ρ (pYd M T) (pNd M T) (pYd M T * pNd M T) hY1 hYN le_rfl
  have hMo := mollM_norm_le χ ρ hre0.le (pYd M T)
  set P := ∑ n ∈ Icc 1 (pNd M T), χ (n : ZMod M) * (n : ℂ) ^ (-ρ) with hPdef
  set Mo := ∑ d ∈ Icc 1 (pYd M T), (((ArithmeticFunction.moebius d : ℤ)) : ℂ) * χ (d : ZMod M) * (d : ℂ) ^ (-ρ)
    with hMdef
  set D := ∑ n ∈ Ioc (pYd M T) (pYd M T * pNd M T), mco (pYd M T) (pNd M T) n * χ (n : ZMod M) * (n : ℂ) ^ (-ρ)
    with hD
  have hnum : ‖P‖ * (pYd M T : ℝ) ≤ 1 / 2 := by
    have hXpos : (0 : ℝ) < X := by linarith
    have hNpos : (0 : ℝ) < pNd M T := by exact_mod_cast hN1
    have hrho : 1 + ‖ρ‖ / ρ.re ≤ 3 * T := by
      have h1 : ‖ρ‖ ≤ ρ.re + T := by
        refine (Complex.norm_le_abs_re_add_abs_im ρ).trans ?_
        rw [abs_of_pos hre0]; linarith
      have h2 : ‖ρ‖ / ρ.re ≤ 1 + T / ρ.re := by
        rw [div_le_iff₀ hre0, add_mul, one_mul, div_mul_cancel₀ _ hre0.ne']; linarith
      have h3 : T / ρ.re ≤ 4 / 3 * T := by
        rw [div_le_iff₀ hre0]; nlinarith
      linarith
    have hpow : ((pNd M T : ℕ) : ℝ) ^ (-ρ.re) ≤ ((pNd M T : ℕ) : ℝ) ^ (-(3 / 4 : ℝ)) :=
      Real.rpow_le_rpow_of_exponent_le (by exact_mod_cast hN1) (by linarith)
    have hN8 : (X : ℝ) ^ (8 : ℕ) ≤ (pNd M T : ℝ) := by exact_mod_cast hNX
    have hpow2 : (X : ℝ) ^ (6 : ℕ) ≤ ((pNd M T : ℕ) : ℝ) ^ (3 / 4 : ℝ) := by
      have e : ((X : ℝ) ^ (8 : ℕ)) ^ (3 / 4 : ℝ) = (X : ℝ) ^ (6 : ℕ) := by
        rw [← Real.rpow_natCast, ← Real.rpow_mul hXpos.le, ← Real.rpow_natCast]
        norm_num
      rw [← e]
      exact Real.rpow_le_rpow (by positivity) hN8 (by norm_num)
    have hinv : ((pNd M T : ℕ) : ℝ) ^ (-(3 / 4 : ℝ)) ≤ 1 / (X : ℝ) ^ (6 : ℕ) := by
      rw [Real.rpow_neg hNpos.le, one_div]
      exact inv_anti₀ (by positivity) hpow2
    have hYr : (pYd M T : ℝ) = (X : ℝ) ^ (3 : ℕ) := by rw [hY, Nat.cast_pow]
    have hc : 2 * ((M : ℝ) + 1) * (1 + ‖ρ‖ / ρ.re) ≤ 8 * X := by
      have hpos : (0 : ℝ) ≤ 1 + ‖ρ‖ / ρ.re := by positivity
      calc 2 * ((M : ℝ) + 1) * (1 + ‖ρ‖ / ρ.re) ≤ 2 * ((M : ℝ) + 1) * (3 * T) :=
            mul_le_mul_of_nonneg_left hrho (by positivity)
        _ ≤ 8 * X := by nlinarith
    have hPle : ‖P‖ ≤ 8 * X * (1 / (X : ℝ) ^ (6 : ℕ)) := by
      refine hP.trans ?_
      have a3 : ((pNd M T : ℕ) : ℝ) ^ (-ρ.re) ≤ 1 / (X : ℝ) ^ (6 : ℕ) := hpow.trans hinv
      calc 2 * ((M : ℝ) + 1) * (1 + ‖ρ‖ / ρ.re) * ((pNd M T : ℕ) : ℝ) ^ (-ρ.re)
          ≤ 8 * X * ((pNd M T : ℕ) : ℝ) ^ (-ρ.re) :=
            mul_le_mul_of_nonneg_right hc (Real.rpow_nonneg (Nat.cast_nonneg _) _)
        _ ≤ 8 * X * (1 / (X : ℝ) ^ (6 : ℕ)) := mul_le_mul_of_nonneg_left a3 (by positivity)
    rw [hYr]
    calc ‖P‖ * (X : ℝ) ^ (3 : ℕ) ≤ 8 * X * (1 / (X : ℝ) ^ (6 : ℕ)) * (X : ℝ) ^ (3 : ℕ) :=
          mul_le_mul_of_nonneg_right hPle (by positivity)
      _ = 8 / X ^ 2 := by
          have hX0 : (X : ℝ) ≠ 0 := hXpos.ne'
          field_simp
      _ ≤ 1 / 2 := by
          rw [div_le_iff₀ (by positivity)]; nlinarith
  have h1D : ‖1 + D‖ ≤ 1 / 2 := by
    rw [← hMI, norm_mul]
    calc ‖P‖ * ‖Mo‖ ≤ ‖P‖ * (pYd M T : ℝ) := mul_le_mul_of_nonneg_left hMo (norm_nonneg _)
      _ ≤ 1 / 2 := hnum
  have hDge : 1 / 2 ≤ ‖D‖ := by
    have := norm_sub_le (1 + D) D
    simp only [add_sub_cancel_right, norm_one] at this
    linarith
  have hsplit : D = ∑ j ∈ range (pJd M T),
      blkD (pYd M T) (pNd M T) (pYd M T * 2 ^ j) (fun n => χ (n : ZMod M)) ρ := by
    rw [hD, show pNd M T = 2 ^ pJd M T by unfold pNd; rfl, sum_blocks]
    rfl
  by_contra hcon
  push Not at hcon
  have hJ8 : 8 ≤ pJd M T := by unfold pJd; omega
  have hJpos : (0 : ℝ) < pJd M T := by exact_mod_cast (by omega : 0 < pJd M T)
  have hlt : ‖D‖ < 1 / 2 := by
    rw [hsplit]
    refine (norm_sum_le _ _).trans_lt ?_
    have hne : (range (pJd M T)).Nonempty := nonempty_range_iff.mpr (by omega)
    calc ∑ j ∈ range (pJd M T), ‖blkD (pYd M T) (pNd M T) (pYd M T * 2 ^ j) (fun n => χ (n : ZMod M)) ρ‖
        < ∑ j ∈ range (pJd M T), 1 / (2 * (pJd M T : ℝ)) := sum_lt_sum_of_nonempty hne hcon
      _ = 1 / 2 := by rw [sum_const, card_range, nsmul_eq_mul]; field_simp
  linarith
end Formalism.HermitianLattices.Ext.PrimesInProgressions.Dens
