-- Prove2me | solution 1 for Formalism.LFunctionChainParameters.LChain.xLargeEv_weakL
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-24T11:05:23.213737+00:00
-- url     : https://prove2.me/submissions/e2b5b082-6075-4070-883b-7f9ce13a03fe

import Definitions.Def_Formalism_SizeWindowBrackets_SChain
import Definitions.Def_Formalism_SizeWindowBrackets_ChainSlopeWindows_LevelOfCongruence
import Definitions.Def_Formalism_SizeWindowBrackets_ChainSlopeWindows_LipschitzWeightAndMinimum
import Definitions.Def_Formalism_SizeWindowBrackets_ChainSlopeWindows_SubThreeMulLogTwoLe
import Definitions.Def_Formalism_SizeWindowBrackets_ChainSlopeWindows_PChain
import Theorems.Thm_Formalism_LFunctionChainParameters_LChain_x_large_eventually

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
namespace Formalism.LFunctionChainParameters.LChain
theorem _root_.solution (K cHH eK Cd ε : ℝ) (h0 : 0 < ε) :
    ∃ x₀ : ℝ, ∀ x : ℝ, x₀ ≤ x → XLarge K cHH eK Cd (x ^ ε / Real.log x) ε x := by
  obtain ⟨x₁, hx₁⟩ := x_large_eventually K cHH eK Cd 0 ε h0
  obtain ⟨x₂, hx₂⟩ := x_large_eventually K cHH eK Cd 0 (ε / 2) (by positivity)
  have e1 : ∀ᶠ x : ℝ in Filter.atTop, (6 : ℝ) ≤ x ^ ((1 : ℝ) / 2) :=
    (tendsto_rpow_atTop (by norm_num)).eventually_ge_atTop _
  have e2 : ∀ᶠ x : ℝ in Filter.atTop, (2 : ℝ) ≤ x ^ (ε / 2) :=
    (tendsto_rpow_atTop (by positivity)).eventually_ge_atTop _
  obtain ⟨x₃, hx₃⟩ := Filter.eventually_atTop.1 (e1.and e2)
  refine ⟨max x₁ (max x₂ x₃), fun x hx => ?_⟩
  have g1 : x₁ ≤ x := le_trans (le_max_left _ _) hx
  have g2 : x₂ ≤ x := le_trans (le_trans (le_max_left _ _) (le_max_right _ _)) hx
  have g3 : x₃ ≤ x := le_trans (le_trans (le_max_right _ _) (le_max_right _ _)) hx
  obtain ⟨a1, a2, a3, -⟩ := hx₁ x g1
  obtain ⟨-, -, -, b4⟩ := hx₂ x g2
  obtain ⟨d1, d2⟩ := hx₃ x g3
  refine ⟨a1, a2, a3, ?_⟩
  have hxpos : 0 < x := by linarith
  have hlog : 0 < Real.log x := Real.log_pos (by linarith)
  unfold moveCost at b4 ⊢
  rw [div_mul_cancel₀ _ hlog.ne']
  have hA : x ^ ((1 : ℝ) / 2 + ε) = x ^ ((1 : ℝ) / 2) * x ^ ε := Real.rpow_add hxpos _ _
  have hB : x ^ ((1 : ℝ) / 2 + ε) = x ^ ((1 : ℝ) / 2 + ε / 2) * x ^ (ε / 2) := by
    rw [← Real.rpow_add hxpos]; congr 1; ring
  have p1 : 0 < x ^ ε := Real.rpow_pos_of_pos hxpos _
  have p2 : 0 < x ^ ((1 : ℝ) / 2 + ε / 2) := Real.rpow_pos_of_pos hxpos _
  have q1 : 6 * x ^ ε ≤ x ^ ((1 : ℝ) / 2 + ε) := by rw [hA]; gcongr
  have q2 : 2 * x ^ ((1 : ℝ) / 2 + ε / 2) ≤ x ^ ((1 : ℝ) / 2 + ε) := by rw [hB]; nlinarith
  simp only [zero_mul, add_zero] at b4
  linarith
end Formalism.LFunctionChainParameters.LChain
