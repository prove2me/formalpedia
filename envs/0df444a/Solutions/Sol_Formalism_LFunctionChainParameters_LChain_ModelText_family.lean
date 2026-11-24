-- Prove2me | solution 1 for Formalism.LFunctionChainParameters.LChain.ModelText.family
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-24T10:46:54.322472+00:00
-- url     : https://prove2.me/submissions/56a1a16e-5029-4a66-bdb2-9846868d1f94

import Definitions.Def_Formalism_SizeWindowBrackets_SChain
import Definitions.Def_Formalism_SizeWindowBrackets_ChainSlopeWindows_LevelOfCongruence
import Definitions.Def_Formalism_SizeWindowBrackets_ChainSlopeWindows_LipschitzWeightAndMinimum
import Definitions.Def_Formalism_SizeWindowBrackets_ChainSlopeWindows_SubThreeMulLogTwoLe
import Definitions.Def_Formalism_SizeWindowBrackets_ChainSlopeWindows_PChain
import Theorems.Thm_Formalism_LFunctionChainParameters_LChain_ModelText_ev_rpow_le_exp
import Theorems.Thm_Formalism_LFunctionChainParameters_LChain_ModelText_famAt
import Theorems.Thm_Formalism_LFunctionChainParameters_LChain_ModelText_cost1
import Theorems.Thm_Formalism_LFunctionChainParameters_LChain_ModelText_cost2
import Theorems.Thm_Formalism_LFunctionChainParameters_LChain_ModelText_wpp1
import Theorems.Thm_Formalism_LFunctionChainParameters_LErr_text_sizes_windows


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
open Formalism.LFunctionChainParameters.LChain.ModelText
namespace Formalism.LFunctionChainParameters.LChain.ModelText
theorem _root_.solution (ε : ℝ) (hε0 : 0 < ε) (hε1 : ε ≤ 1) : ∃ x₀ : ℝ, ∀ x : ℝ, x₀ ≤ x → FamAt ε x := by
  obtain ⟨x1, hx1⟩ := text_sizes_windows ε 15 hε0
  have e1 := ev_rpow_le_exp 18 (ε / 8) (by positivity)
  have e2 := ev_rpow_le_exp 18 (ε / 4) (by positivity)
  have e3 := ev_rpow_le_exp 15 (ε / 3) (by positivity)
  have e4 : ∀ᶠ x : ℝ in Filter.atTop, (2 : ℝ) ≤ x ^ (9 * ε / 16) :=
    (tendsto_rpow_atTop (by positivity)).eventually_ge_atTop _
  have e5 : ∀ᶠ x : ℝ in Filter.atTop, (2 : ℝ) ≤ x ^ (3 * ε / 4) :=
    (tendsto_rpow_atTop (by positivity)).eventually_ge_atTop _
  have e6 : ∀ᶠ x : ℝ in Filter.atTop, (2 : ℝ) ≤ x ^ (2 * ε / 3) :=
    (tendsto_rpow_atTop (by positivity)).eventually_ge_atTop _
  obtain ⟨x0, hx0⟩ := Filter.eventually_atTop.1
    (((((((e1.and e2).and e3).and e4).and e5).and e6).and (Filter.eventually_ge_atTop (48 : ℝ))).and
      (Filter.eventually_ge_atTop x1))
  refine ⟨x0, fun x hx => ?_⟩
  obtain ⟨⟨⟨⟨⟨⟨⟨f1, f2⟩, f3⟩, f4⟩, f5⟩, f6⟩, h48⟩, hxx1⟩ := hx0 x hx
  have hxpos : 0 < x := by linarith
  have hx1' : 1 ≤ x := by linarith

  set y : ℝ := x ^ (2 + 8 * ε) with hy
  have hy1 : 1 ≤ y := Real.one_le_rpow hx1' (by linarith)
  set n : ℕ := ⌈y⌉₊ with hn
  have hnpos : 0 < n := Nat.ceil_pos.2 (by linarith)
  have : NeZero n := ⟨hnpos.ne'⟩
  have hnlo : y ≤ (n : ℝ) := Nat.le_ceil y
  have hnhi : (n : ℝ) ≤ 2 * y := by
    have := (Nat.ceil_lt_add_one (by linarith : 0 ≤ y)).le
    linarith
  have hn0 : (0 : ℝ) < n := by exact_mod_cast hnpos
  have hn15 : (n : ℝ) ≤ x ^ (15 : ℝ) := by
    have h1 : 2 * y ≤ x ^ (1 : ℝ) * y := by rw [Real.rpow_one]; nlinarith
    rw [hy, ← Real.rpow_add hxpos] at h1
    exact hnhi.trans (h1.trans (Real.rpow_le_rpow_of_exponent_le hx1' (by linarith)))

  set z : ℝ := x ^ ((1 : ℝ) / 2 - ε / 16) with hz
  have hz1 : 1 ≤ z := Real.one_le_rpow hx1' (by linarith)
  set m : ℕ := ⌈z⌉₊ with hm
  have hmlo : z ≤ (m : ℝ) := Nat.le_ceil z
  have hmhi : (m : ℝ) ≤ 2 * z := by
    have := (Nat.ceil_lt_add_one (by linarith : 0 ≤ z)).le
    linarith
  have hcard : Fintype.card (ZMod n) = n := ZMod.card n

  have hd1 : x ^ (-(ε / 8)) ≤ 1 := Real.rpow_le_one_of_one_le_of_nonpos hx1' (by linarith)
  have hd1' : 0 < x ^ (-(ε / 8)) := Real.rpow_pos_of_pos hxpos _
  have hd2 : x ^ (-ε) ≤ 1 := Real.rpow_le_one_of_one_le_of_nonpos hx1' (by linarith)
  have hd2' : 0 < x ^ (-ε) := Real.rpow_pos_of_pos hxpos _
  obtain ⟨TT, -, hTTc⟩ := Finset.exists_subset_card_eq (s := (univ : Finset (ZMod n)))
    (n := ⌈x ^ (-(ε / 8)) * n / 2⌉₊) (by
      rw [Finset.card_univ, hcard]
      exact Nat.ceil_le.2 (by nlinarith))
  obtain ⟨T2, -, hT2c⟩ := Finset.exists_subset_card_eq (s := (univ : Finset (ZMod n)))
    (n := ⌈x ^ (-ε) * n⌉₊) (by
      rw [Finset.card_univ, hcard]
      exact Nat.ceil_le.2 (by nlinarith))
  have hk15 : kTx x ε ≤ x ^ (15 : ℝ) := Real.rpow_le_rpow_of_exponent_le hx1' (by linarith)
  have hk0 : 0 < kTx x ε := Real.rpow_pos_of_pos hxpos _
  have hT := hx1 x (kTx x ε) n (x ^ (ε / 3)) hxx1 hk0 hk15 hn0 hn15 (le_refl _)
  refine ⟨n, inferInstance, m, TT, T2, hnlo, hnhi, hmlo, hmhi, ?_, ?_, ?_⟩
  · rw [hTTc]; exact Nat.ceil_lt_add_one (by positivity)
  · rw [hT2c]; exact Nat.ceil_lt_add_one (by positivity)
  · refine famAt x ε m TT T2 hε0 hε1 (by linarith) ?_ ?_ hmlo hmhi f4 ?_ ?_ ?_ ?_ ?_
    · rw [hcard]; exact hT
    · rw [hcard]; exact hnlo
    · rw [hcard, hTTc]; exact Nat.le_ceil _
    · rw [hcard, hT2c]; exact Nat.le_ceil _
    · rw [hcard]; exact cost1 h48 hn0 hn15 f1
    · rw [hcard]; exact cost2 h48 hn0 hn15 f2 f5
    · rw [hcard]; exact wpp1 h48 hn0 hn15 f3 f6
end Formalism.LFunctionChainParameters.LChain.ModelText
