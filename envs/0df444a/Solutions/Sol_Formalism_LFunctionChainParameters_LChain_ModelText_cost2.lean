-- Prove2me | solution 1 for Formalism.LFunctionChainParameters.LChain.ModelText.cost2
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-24T10:29:32.103639+00:00
-- url     : https://prove2.me/submissions/0497bcf6-d8ec-41be-b3ec-19d8b0b9347e

import Definitions.Def_Formalism_SizeWindowBrackets_SChain
import Definitions.Def_Formalism_SizeWindowBrackets_ChainSlopeWindows_LevelOfCongruence
import Definitions.Def_Formalism_SizeWindowBrackets_ChainSlopeWindows_LipschitzWeightAndMinimum
import Definitions.Def_Formalism_SizeWindowBrackets_ChainSlopeWindows_SubThreeMulLogTwoLe
import Definitions.Def_Formalism_SizeWindowBrackets_ChainSlopeWindows_PChain
import Theorems.Thm_Formalism_LFunctionChainParameters_LChain_ModelText_h18

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
theorem _root_.solution {x ε n : ℝ} (h48 : 48 ≤ x) (hn0 : 0 < n) (hn15 : n ≤ x ^ (15 : ℝ))
    (f2 : x ^ (18 : ℝ) ≤ Real.exp (x ^ (ε / 4))) (f5 : 2 ≤ x ^ (3 * ε / 4)) :
    6 * (2 * n) * (x + 1) * (etaTx x ε + 1) ≤ bTx x ε / x := by
  have hxpos : 0 < x := by linarith
  have hp15 : 0 < x ^ (15 : ℝ) := Real.rpow_pos_of_pos hxpos _
  rw [le_div_iff₀ hxpos]
  unfold etaTx bTx
  obtain ⟨E, hE⟩ : ∃ E, E = Real.exp (x ^ (ε / 4)) := ⟨_, rfl⟩
  have hE1 : 1 ≤ E := by rw [hE]; exact Real.one_le_exp (Real.rpow_nonneg hxpos.le _)
  have hEE : E * E ≤ Real.exp (x ^ ε) := by
    rw [hE, ← Real.exp_add]
    apply Real.exp_le_exp.2
    have h : x ^ ε = x ^ (3 * ε / 4) * x ^ (ε / 4) := by
      rw [← Real.rpow_add hxpos]; congr 1; ring
    rw [h]
    have := Real.rpow_nonneg hxpos.le (ε / 4)
    nlinarith
  rw [← hE] at f2 ⊢
  have h1 : 6 * (2 * n) * (x + 1) * x * 2 ≤ E := by
    refine le_trans ?_ f2
    rw [h18 hxpos]
    have h2 : 6 * (2 * n) * (x + 1) * x * 2 ≤ 6 * (2 * x ^ (15 : ℝ)) * (x + 1) * x * 2 := by gcongr
    have h3 : 6 * (2 * x ^ (15 : ℝ)) * (x + 1) * x * 2 ≤ x ^ (15 : ℝ) * x * x * x := by
      have h4 : 24 * (x + 1) ≤ x * x := by nlinarith
      have h5 : 0 < x ^ (15 : ℝ) * x := by positivity
      calc 6 * (2 * x ^ (15 : ℝ)) * (x + 1) * x * 2 = (x ^ (15 : ℝ) * x) * (24 * (x + 1)) := by ring
        _ ≤ (x ^ (15 : ℝ) * x) * (x * x) := by gcongr
        _ = x ^ (15 : ℝ) * x * x * x := by ring
    linarith
  calc 6 * (2 * n) * (x + 1) * (E + 1) * x ≤ 6 * (2 * n) * (x + 1) * (2 * E) * x := by
        gcongr; linarith
    _ = (6 * (2 * n) * (x + 1) * x * 2) * E := by ring
    _ ≤ E * E := by gcongr
    _ ≤ Real.exp (x ^ ε) := hEE
end Formalism.LFunctionChainParameters.LChain.ModelText
