-- Prove2me | solution 1 for Formalism.LFunctionChainParameters.LChain.ModelEv.sizesEv
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-24T11:38:55.892109+00:00
-- url     : https://prove2.me/submissions/d1532d09-3066-43a2-b847-d922172e3ec9

import Definitions.Def_Formalism_SizeWindowBrackets_SChain
import Definitions.Def_Formalism_SizeWindowBrackets_ChainSlopeWindows_LevelOfCongruence
import Definitions.Def_Formalism_SizeWindowBrackets_ChainSlopeWindows_LipschitzWeightAndMinimum
import Definitions.Def_Formalism_SizeWindowBrackets_ChainSlopeWindows_SubThreeMulLogTwoLe
import Definitions.Def_Formalism_SizeWindowBrackets_ChainSlopeWindows_PChain
import Theorems.Thm_Formalism_LFunctionChainParameters_LChain_x_large_eventually
import Theorems.Thm_Formalism_LFunctionChainParameters_LChain_ModelEv_sizesOf
import Theorems.Thm_Formalism_LFunctionChainParameters_LErr_large_x_eventually


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Finset
noncomputable section
open Formalism Formalism.LFunctionChainParameters Formalism.LFunctionChainParameters.LChain
open Formalism Formalism.D5 Formalism.RankGapBounds.WeightedMeanData Formalism.LFunctionChainParameters.WeightedSlopeBounds Formalism.LFunctionChainParameters.characterSumData Formalism.LFunctionChainParameters.ThickSetMeanBounds Formalism.LFunctionChainParameters.ConditionalMainTheorem Formalism.LFunctionChainParameters.LErr
open Formalism.LFunctionChainParameters.LChain.ModelEv
open Model
namespace Formalism.LFunctionChainParameters.LChain.ModelEv
theorem _root_.solution : ∀ ε : ℝ, 0 < ε → ε ≤ 1 / 2 → ∃ x₀ : ℝ, ∀ x : ℝ, x₀ ≤ x →
    SizesAt 1 1 2 ε x ∧ XLarge 1 1 2 0 0 ε x := by
  intro ε hε0 hε2
  obtain ⟨x₁, hx₁⟩ := x_large_eventually 1 1 2 0 0 ε hε0
  obtain ⟨x₂, hx₂⟩ := Formalism.LFunctionChainParameters.LErr.large_x_eventually (ε / 2) 0 0 0 (by positivity)
  refine ⟨max (max x₁ x₂) 48, fun x hx => ?_⟩
  have hXL := hx₁ x (le_trans (le_trans (le_max_left _ _) (le_max_left _ _)) hx)
  obtain ⟨hlog, hbig⟩ := hx₂ x (le_trans (le_trans (le_max_right _ _) (le_max_left _ _)) hx)
  have hx48 : 48 ≤ x := le_trans (le_max_right _ _) hx
  refine ⟨?_, hXL⟩
  have hx0 : 0 < x := by linarith
  have hx1 : 1 ≤ x := by linarith
  obtain ⟨-, h26, -, -⟩ := hXL
  set n : ℕ := ⌈x⌉₊ with hn
  set u : ℝ := x ^ ((1 : ℝ) / 2 - ε) with hu
  set m : ℕ := ⌈u⌉₊ with hm
  have hnx : x ≤ n := Nat.le_ceil x
  have hnx1 : (n : ℝ) ≤ x + 1 := (Nat.ceil_lt_add_one hx0.le).le
  have hu1 : 1 ≤ u := Real.one_le_rpow hx1 (by linarith)
  have hmu : u ≤ m := Nat.le_ceil u
  have hmu1 : (m : ℝ) ≤ u + 1 := (Nat.ceil_lt_add_one (by linarith)).le
  have h2 : (2 : ℝ) ≤ x ^ (3 * ε / 2) := by
    have : x ^ (3 * ε / 8) ≤ x ^ (3 * ε / 2) := Real.rpow_le_rpow_of_exponent_le hx1 (by linarith)
    linarith
  have hsplit : x ^ ((1 : ℝ) / 2 + ε / 2) = u * x ^ (3 * ε / 2) := by
    rw [hu, ← Real.rpow_add hx0]
    congr 1
    ring
  have hm2 : (m : ℝ) ≤ x ^ ((1 : ℝ) / 2 + ε / 2) := by
    rw [hsplit]
    nlinarith
  have hmx : (m : ℝ) ≤ x := by
    have : x ^ ((1 : ℝ) / 2 + ε / 2) ≤ x ^ (1 : ℝ) := Real.rpow_le_rpow_of_exponent_le hx1 (by linarith)
    rw [Real.rpow_one] at this
    linarith
  have hk : x * m ≤ (n : ℝ) ^ 2 * u := by
    have h3 : x * m ≤ x * (2 * u) := mul_le_mul_of_nonneg_left (by linarith) hx0.le
    have h4 : x * 2 ≤ (n : ℝ) ^ 2 := by nlinarith
    nlinarith
  set b : ℝ := 12 * n * (x + 1) * x with hb
  have hn0 : (0 : ℝ) < n := by linarith
  have hb0 : 0 < b := by rw [hb]; positivity
  have hb4 : b ≤ x ^ 4 := by
    have e1 : b ≤ 12 * (x + 1) * (x + 1) * x := by
      rw [hb]
      have : 12 * (n : ℝ) * (x + 1) ≤ 12 * (x + 1) * (x + 1) := by nlinarith
      nlinarith
    have e2 : 12 * (x + 1) * (x + 1) * x ≤ 48 * x ^ 3 := by nlinarith [mul_pos hx0 hx0]
    have e3 : 48 * x ^ 3 ≤ x ^ 4 := by
      have : 0 ≤ x ^ 3 := by positivity
      nlinarith
    linarith
  have hL : Real.log b ≤ 2 * x ^ ε := by
    have e1 : Real.log b ≤ 4 * Real.log x := by
      have := Real.log_le_log hb0 hb4
      rw [Real.log_pow] at this
      simpa using this
    have e2 : x ^ ε = x ^ (ε / 2) * x ^ (ε / 2) := by
      rw [← Real.rpow_add hx0]
      congr 1
      ring
    have e3 : (200 : ℝ) ≤ x ^ (ε / 2) := by
      have : KBig 0 0 0 = 200 := by norm_num [KBig]
      rw [this] at hbig
      exact hbig
    rw [e2]
    nlinarith
  have : NeZero n := ⟨by
    intro h0
    rw [h0] at hn0
    simp at hn0⟩
  exact sizesOf (H := ZMod n) x ε b m ⌈x * b⌉₊ n (ZMod.card n) (by linarith) hε0 (by linarith) hnx hb hmu hm2 hmx hk hL
    (Nat.le_ceil _) (by
      rw [Real.le_log_iff_exp_le hx0]
      have h1 : Real.exp 3 = Real.exp 1 ^ 3 := by
        rw [← Real.exp_nat_mul]
        norm_num
      have h2 := Real.exp_one_lt_d9
      have h3 : Real.exp 1 ^ 3 ≤ 2.7182818286 ^ 3 := pow_le_pow_left₀ (Real.exp_pos 1).le h2.le 3
      rw [h1]
      have h4 : (2.7182818286 : ℝ) ^ 3 ≤ 48 := by norm_num
      linarith)
end Formalism.LFunctionChainParameters.LChain.ModelEv
