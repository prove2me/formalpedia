-- Prove2me | solution 1 for Formalism.HermitianLattices.Ext.PrimitiveCharacterCasts.ZD.zero_detection
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-24T12:47:18.176537+00:00
-- url     : https://prove2.me/submissions/116736f3-fd60-417f-976b-b06b33b105f5

import Definitions.Def_Formalism_GL3MeanSquares_GenusMeanAsymptotics_JacobiCharacterSums_CountZDefs
import Definitions.Def_Formalism_GL3MeanSquares_GenusMeanAsymptotics_JacobiCharacterSums_CountZDetect
import Theorems.Thm_Formalism_HermitianLattices_Ext_PrimitiveCharacterCasts_ZD_sum_blocks
import Theorems.Thm_Formalism_HermitianLattices_Ext_PrimitiveCharacterCasts_ZD_mollM_norm_le
import Theorems.Thm_Formalism_FX_l_function_partial_sum
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
open scoped ArithmeticFunction.Moebius
noncomputable section
open Formalism Formalism.HermitianLattices Formalism.HermitianLattices.Ext Formalism.HermitianLattices.Ext.PrimitiveCharacterCasts Formalism.HermitianLattices.Ext.PrimitiveCharacterCasts.ZD
attribute [local irreducible] q0 pY pJ pN
namespace Formalism.HermitianLattices.Ext.PrimitiveCharacterCasts.ZD
theorem _root_.solution : DetectOf := by
  intro hM Q hQ p hp hp1 hpQ ρ hρ hρim hL
  obtain ⟨N0, χ⟩ := p
  simp only at hp hp1 hpQ hL
  obtain ⟨X, hX⟩ : ∃ X : ℕ, q0 Q = X := ⟨_, rfl⟩
  have hXQ : Q ≤ (X : ℝ) := by rw [← hX]; unfold q0; exact Nat.le_ceil Q
  have hX20 : (20 : ℝ) ≤ X := le_trans hQ hXQ
  have hX1 : 1 ≤ X := by exact_mod_cast (show (1 : ℝ) ≤ X by linarith)
  have hs0 : s0 = 399 / 400 := by unfold s0; norm_num
  have hre0 : 0 < ρ.re := by rw [hs0] at hρ; linarith

  have hχ1 : χ ≠ 1 := by
    intro h
    have hc : χ.conductor = N0 + 1 := hp
    rw [h, DirichletCharacter.conductor_one] at hc
    omega

  have hJ8 : 8 ≤ pJ Q := by unfold pJ; omega
  have hNX : X ^ 8 ≤ pN Q := by
    have h := Nat.lt_pow_succ_log_self (by norm_num : 1 < 2) X
    unfold pN pJ
    rw [hX, mul_comm 8, pow_mul]
    exact Nat.pow_le_pow_left h.le 8
  have hY : pY Q = X ^ 4 := by unfold pY; rw [hX]
  have hYN : pY Q ≤ pN Q := by
    rw [hY]; exact le_trans (Nat.pow_le_pow_right hX1 (by norm_num)) hNX
  have hY1 : 1 ≤ pY Q := by rw [hY]; exact Nat.one_le_pow _ _ (by omega)
  have hN1 : 1 ≤ pN Q := le_trans hY1 hYN

  have hB := Formalism.ZeroFreeDirichlet.norm_character_sum_Icc_le χ hχ1
  have hP := Formalism.FX.l_function_partial_sum (N0 + 1) χ hχ1 _ hB ρ hre0 (pN Q) hN1
  rw [hL, zero_sub, norm_neg] at hP

  have hMI := hM (N0 + 1) χ ρ (pY Q) (pN Q) (pY Q * pN Q) hY1 hYN le_rfl
  have hMo := mollM_norm_le χ ρ hre0.le (pY Q)
  set P := ∑ n ∈ Icc 1 (pN Q), χ (n : ZMod (N0 + 1)) * (n : ℂ) ^ (-ρ) with hPdef
  set Mo := ∑ d ∈ Icc 1 (pY Q), (((μ d : ℤ)) : ℂ) * χ (d : ZMod (N0 + 1)) * (d : ℂ) ^ (-ρ) with hMdef
  set D := ∑ n ∈ Ioc (pY Q) (pY Q * pN Q), mco (pY Q) (pN Q) n * χ (n : ZMod (N0 + 1)) * (n : ℂ) ^ (-ρ) with hD

  have hnum : ‖P‖ * (pY Q : ℝ) ≤ 1 / 2 := by
    have hq : ((N0 + 1 : ℕ) : ℝ) + 1 ≤ 2 * X := by
      have : ((N0 + 1 : ℕ) : ℝ) ≤ Q := hpQ
      linarith
    have hrho : 1 + ‖ρ‖ / ρ.re ≤ 3 * X := by
      have h1 : ‖ρ‖ ≤ ρ.re + Q := by
        refine (Complex.norm_le_abs_re_add_abs_im ρ).trans ?_
        rw [abs_of_pos hre0]; linarith
      have h2 : ‖ρ‖ / ρ.re ≤ 1 + Q / ρ.re := by
        rw [div_le_iff₀ hre0]; rw [add_mul, one_mul, div_mul_cancel₀ _ hre0.ne']; linarith
      have h3 : Q / ρ.re ≤ 2 * Q := by
        rw [div_le_iff₀ hre0]; rw [hs0] at hρ; nlinarith
      linarith
    have hNpos : (0 : ℝ) < pN Q := by exact_mod_cast hN1
    have hXpos : (0 : ℝ) < X := by linarith
    have hpow : ((pN Q : ℕ) : ℝ) ^ (-ρ.re) ≤ ((pN Q : ℕ) : ℝ) ^ (-(15 / 16 : ℝ)) :=
      Real.rpow_le_rpow_of_exponent_le (by exact_mod_cast hN1) (by rw [hs0] at hρ; linarith)
    have hN8 : (X : ℝ) ^ (8 : ℕ) ≤ (pN Q : ℝ) := by exact_mod_cast hNX
    have hpow2 : 4 * (X : ℝ) ^ (7 : ℕ) ≤ ((pN Q : ℕ) : ℝ) ^ (15 / 16 : ℝ) := by
      have e : ((X : ℝ) ^ (8 : ℕ)) ^ (15 / 16 : ℝ) = (X : ℝ) ^ (7 : ℕ) * Real.sqrt X := by
        rw [← Real.rpow_natCast, ← Real.rpow_mul hXpos.le, Real.sqrt_eq_rpow, ← Real.rpow_natCast,
          ← Real.rpow_add hXpos]
        norm_num
      have hs : (4 : ℝ) ≤ Real.sqrt X := by
        rw [show (4 : ℝ) = Real.sqrt 16 by rw [show (16 : ℝ) = 4 ^ 2 by norm_num, Real.sqrt_sq (by norm_num)]]
        exact Real.sqrt_le_sqrt (by linarith)
      calc 4 * (X : ℝ) ^ (7 : ℕ) ≤ (X : ℝ) ^ (7 : ℕ) * Real.sqrt X := by
            have : (0 : ℝ) ≤ (X : ℝ) ^ (7 : ℕ) := by positivity
            rw [mul_comm]; exact mul_le_mul_of_nonneg_left hs this
        _ = ((X : ℝ) ^ (8 : ℕ)) ^ (15 / 16 : ℝ) := e.symm
        _ ≤ _ := Real.rpow_le_rpow (by positivity) hN8 (by norm_num)
    have hinv : ((pN Q : ℕ) : ℝ) ^ (-(15 / 16 : ℝ)) ≤ 1 / (4 * (X : ℝ) ^ (7 : ℕ)) := by
      rw [Real.rpow_neg hNpos.le, one_div]
      exact inv_anti₀ (by positivity) hpow2
    have hYr : (pY Q : ℝ) = (X : ℝ) ^ (4 : ℕ) := by rw [hY, Nat.cast_pow]
    have hPle : ‖P‖ ≤ 2 * (2 * X) * (3 * X) * (1 / (4 * (X : ℝ) ^ (7 : ℕ))) := by
      refine hP.trans ?_
      have hpos1 : (0 : ℝ) ≤ ((N0 + 1 : ℕ) : ℝ) + 1 := by positivity
      have hpos2 : (0 : ℝ) ≤ 1 + ‖ρ‖ / ρ.re := by positivity
      have a1 : 2 * (((N0 + 1 : ℕ) : ℝ) + 1) ≤ 2 * (2 * X) := by linarith
      have a12 : 2 * (((N0 + 1 : ℕ) : ℝ) + 1) * (1 + ‖ρ‖ / ρ.re) ≤ 2 * (2 * X) * (3 * X) :=
        mul_le_mul a1 hrho hpos2 (by positivity)
      have a3 : ((pN Q : ℕ) : ℝ) ^ (-ρ.re) ≤ 1 / (4 * (X : ℝ) ^ (7 : ℕ)) := hpow.trans hinv
      calc 2 * (((N0 + 1 : ℕ) : ℝ) + 1) * (1 + ‖ρ‖ / ρ.re) * ((pN Q : ℕ) : ℝ) ^ (-ρ.re)
          ≤ 2 * (2 * X) * (3 * X) * ((pN Q : ℕ) : ℝ) ^ (-ρ.re) :=
            mul_le_mul_of_nonneg_right a12 (Real.rpow_nonneg (Nat.cast_nonneg _) _)
        _ ≤ 2 * (2 * X) * (3 * X) * (1 / (4 * (X : ℝ) ^ (7 : ℕ))) :=
            mul_le_mul_of_nonneg_left a3 (by positivity)
    rw [hYr]
    calc ‖P‖ * (X : ℝ) ^ (4 : ℕ) ≤ 2 * (2 * X) * (3 * X) * (1 / (4 * (X : ℝ) ^ (7 : ℕ))) * (X : ℝ) ^ (4 : ℕ) :=
          mul_le_mul_of_nonneg_right hPle (by positivity)
      _ = 3 / X := by
          have hX0 : (X : ℝ) ≠ 0 := hXpos.ne'
          rw [eq_div_iff hX0]
          field_simp
          ring
      _ ≤ 1 / 2 := by rw [div_le_iff₀ hXpos]; linarith
  have h1D : ‖1 + D‖ ≤ 1 / 2 := by
    rw [← hMI]
    rw [norm_mul]
    calc ‖P‖ * ‖Mo‖ ≤ ‖P‖ * (pY Q : ℝ) := mul_le_mul_of_nonneg_left hMo (norm_nonneg _)
      _ ≤ 1 / 2 := hnum
  have hDge : 1 / 2 ≤ ‖D‖ := by
    have := norm_sub_le (1 + D) D
    simp only [add_sub_cancel_right, norm_one] at this
    linarith

  have hsplit : D = ∑ j ∈ range (pJ Q), blk (pY Q) (pN Q) (pY Q * 2 ^ j) ⟨N0, χ⟩ ρ := by
    rw [hD, show pN Q = 2 ^ pJ Q by unfold pN; rfl, sum_blocks]
    rfl
  by_contra hcon
  push_neg at hcon
  have hJpos : (0 : ℝ) < pJ Q := by exact_mod_cast (by omega : 0 < pJ Q)
  have hlt : ‖D‖ < 1 / 2 := by
    rw [hsplit]
    refine (norm_sum_le _ _).trans_lt ?_
    have hne : (range (pJ Q)).Nonempty := nonempty_range_iff.mpr (by omega)
    calc ∑ j ∈ range (pJ Q), ‖blk (pY Q) (pN Q) (pY Q * 2 ^ j) ⟨N0, χ⟩ ρ‖
        < ∑ j ∈ range (pJ Q), 1 / (2 * (pJ Q : ℝ)) := sum_lt_sum_of_nonempty hne hcon
      _ = 1 / 2 := by rw [sum_const, card_range, nsmul_eq_mul]; field_simp
  linarith
end Formalism.HermitianLattices.Ext.PrimitiveCharacterCasts.ZD
