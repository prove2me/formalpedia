-- Prove2me | solution 1 for Formalism.HermitianLattices.Ext.PrimesInProgressions.Hyp.diff_bound
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-25T09:19:35.757378+00:00
-- url     : https://prove2.me/submissions/15cc60d9-08b2-4fec-92c2-62329891c637

import Definitions.Def_Formalism_GL3MeanSquares_GenusMeanAsymptotics_JacobiCharacterSums_DHFinish2Of
import Definitions.Def_Formalism_GL3MeanSquares_GenusMeanAsymptotics_JacobiCharacterSums_PNTDHHyperC
import Definitions.Def_Formalism_GL3MeanSquares_GenusMeanAsymptotics_JacobiCharacterSums_PNTDHHyper
import Theorems.Thm_Formalism_HermitianLattices_Ext_PrimesInProgressions_Hyp_g_mono
import Theorems.Thm_Formalism_HermitianLattices_Ext_PrimesInProgressions_Hyp_cF_approx
import Theorems.Thm_Formalism_HermitianLattices_Ext_PrimesInProgressions_Hyp_cT_diff


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Finset Complex Classical
noncomputable section
open Formalism Formalism.HermitianLattices Formalism.HermitianLattices.Ext Formalism.HermitianLattices.Ext.PrimesInProgressions
open Formalism.HermitianLattices.Ext.LogarithmicIntegralBounds Formalism.ZeroFreeDirichlet
open Formalism.HermitianLattices.Ext.PrimesInProgressions.Hyp
variable {q : ℕ} [NeZero q] (χ : DirichletCharacter ℂ q)
namespace Formalism.HermitianLattices.Ext.PrimesInProgressions.Hyp
theorem _root_.solution (hχ : χ ≠ 1) (N₀ N₁ : ℕ) (h0 : 1 ≤ N₀) (h01 : N₀ ≤ N₁) :
    (cF χ N₁ - cF χ N₀).re ≤ ‖DirichletCharacter.LFunction χ 1‖ * (Real.log N₁ - Real.log N₀) +
      86 * ((q : ℝ) + 1) * ((Real.log N₀ + 1) / √(N₀ : ℝ)) := by
  set L := DirichletCharacter.LFunction χ 1
  set U₀ := Nat.sqrt N₀ with hU₀
  set U₁ := Nat.sqrt N₁ with hU₁
  set B := (q : ℝ) + 1 with hBdef
  have hB : 1 ≤ B := by have := Nat.cast_nonneg (α := ℝ) q; linarith
  have hN0r : (1 : ℝ) ≤ N₀ := by exact_mod_cast h0
  have hN01r : (N₀ : ℝ) ≤ N₁ := by exact_mod_cast h01
  have hU01 : U₀ ≤ U₁ := Nat.sqrt_le_sqrt h01
  have hU0 : 1 ≤ U₀ := Nat.sqrt_pos.mpr (by omega)
  have hR1 := cF_approx χ hχ N₁ (by omega)
  have hR0 := cF_approx χ hχ N₀ h0
  have hT := cT_diff χ hχ U₀ U₁ hU0 hU01
  set R₁ := cF χ N₁ - (((Real.log N₁ + Real.eulerMascheroniConstant : ℝ) : ℂ) * L - cT χ U₁)
  set R₀ := cF χ N₀ - (((Real.log N₀ + Real.eulerMascheroniConstant : ℝ) : ℂ) * L - cT χ U₀)
  set t := Real.log N₁ - Real.log N₀ with ht
  have ht0 : 0 ≤ t := by
    have := Real.log_le_log (by linarith) hN01r; linarith
  set W := -(cT χ U₁ - cT χ U₀) + R₁ - R₀ with hW
  have eD : cF χ N₁ - cF χ N₀ = (t : ℂ) * L + W := by
    simp only [hW, R₁, R₀, ht]; push_cast; ring
  rw [eD, Complex.add_re, Complex.re_ofReal_mul]
  have hLre : L.re ≤ ‖L‖ := Complex.re_le_norm L
  have hWre : W.re ≤ ‖W‖ := Complex.re_le_norm W
  have hWn : ‖W‖ ≤ ‖cT χ U₁ - cT χ U₀‖ + ‖R₁‖ + ‖R₀‖ := by
    rw [hW]
    calc ‖-(cT χ U₁ - cT χ U₀) + R₁ - R₀‖ ≤ ‖-(cT χ U₁ - cT χ U₀) + R₁‖ + ‖R₀‖ := norm_sub_le _ _
      _ ≤ ‖-(cT χ U₁ - cT χ U₀)‖ + ‖R₁‖ + ‖R₀‖ := by gcongr; exact norm_add_le _ _
      _ = _ := by rw [norm_neg]
  have hg := g_mono (N₀ : ℝ) (N₁ : ℝ) hN0r hN01r
  set g₀ := (Real.log N₀ + 1) / √(N₀ : ℝ)
  have hg0 : 0 ≤ g₀ := div_nonneg (by linarith [Real.log_natCast_nonneg N₀]) (Real.sqrt_nonneg _)
  have hR1' : ‖R₁‖ ≤ 52 * B * g₀ := by
    have e : 26 * B * (Real.log N₁ + 1) / √(N₁ : ℝ) = 26 * B * ((Real.log N₁ + 1) / √(N₁ : ℝ)) := by ring
    rw [e] at hR1
    have := mul_le_mul_of_nonneg_left hg (by positivity : (0 : ℝ) ≤ 26 * B)
    nlinarith
  have hR0' : ‖R₀‖ ≤ 26 * B * g₀ := by
    have e : 26 * B * (Real.log N₀ + 1) / √(N₀ : ℝ) = 26 * B * g₀ := by ring
    rw [e] at hR0; exact hR0
  have hT' : ‖cT χ U₁ - cT χ U₀‖ ≤ 8 * B * g₀ := by
    have hUr : (1 : ℝ) ≤ U₀ := by exact_mod_cast hU0
    have hUN : U₀ ≤ N₀ := Nat.sqrt_le_self N₀
    have hUNr : (U₀ : ℝ) ≤ N₀ := by exact_mod_cast hUN
    have hlt : N₀ < (U₀ + 1) * (U₀ + 1) := Nat.lt_succ_sqrt N₀
    have hltr : (N₀ : ℝ) < ((U₀ : ℝ) + 1) * ((U₀ : ℝ) + 1) := by exact_mod_cast hlt
    have hsU : √(N₀ : ℝ) < (U₀ : ℝ) + 1 := by
      have := Real.sqrt_lt_sqrt (Nat.cast_nonneg N₀) hltr
      rwa [Real.sqrt_mul_self (by linarith)] at this
    have hs0 : 0 < √(N₀ : ℝ) := Real.sqrt_pos.mpr (by linarith)
    have hlog : Real.log ((U₀ : ℝ) + 1) ≤ 1 + Real.log N₀ := by
      have h1 : Real.log ((U₀ : ℝ) + 1) ≤ Real.log (2 * N₀) := Real.log_le_log (by linarith) (by linarith)
      rw [Real.log_mul (by norm_num) (by linarith)] at h1
      have := Real.log_two_lt_d9
      linarith
    have hln : 0 ≤ Real.log N₀ := Real.log_natCast_nonneg N₀
    have h2 : (1 + Real.log ((U₀ : ℝ) + 1)) / ((U₀ : ℝ) + 1) ≤ 2 * g₀ := by
      have e : 2 * g₀ = 2 * (Real.log N₀ + 1) / √(N₀ : ℝ) := by ring
      rw [e, div_le_div_iff₀ (by linarith) hs0]
      nlinarith
    have := mul_le_mul_of_nonneg_left h2 (by positivity : (0 : ℝ) ≤ 4 * B)
    linarith
  have hLt : t * L.re ≤ ‖L‖ * t := by nlinarith
  linarith
end Formalism.HermitianLattices.Ext.PrimesInProgressions.Hyp
