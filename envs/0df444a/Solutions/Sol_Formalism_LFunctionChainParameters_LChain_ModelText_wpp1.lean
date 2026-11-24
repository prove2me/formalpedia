-- Prove2me | solution 1 for Formalism.LFunctionChainParameters.LChain.ModelText.wpp1
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-24T10:29:33.445866+00:00
-- url     : https://prove2.me/submissions/dd261c9f-e215-423a-a9df-52a75a766f61

import Definitions.Def_Formalism_SizeWindowBrackets_SChain
import Definitions.Def_Formalism_SizeWindowBrackets_ChainSlopeWindows_LevelOfCongruence
import Definitions.Def_Formalism_SizeWindowBrackets_ChainSlopeWindows_LipschitzWeightAndMinimum
import Definitions.Def_Formalism_SizeWindowBrackets_ChainSlopeWindows_SubThreeMulLogTwoLe
import Definitions.Def_Formalism_SizeWindowBrackets_ChainSlopeWindows_PChain

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
    (f3 : x ^ (15 : ℝ) ≤ Real.exp (x ^ (ε / 3))) (f6 : 2 ≤ x ^ (2 * ε / 3)) : 1 ≤ wppTx x ε n := by
  have hxpos : 0 < x := by linarith
  unfold wppTx bpTx aTx bTx XpTx
  obtain ⟨X, hX⟩ : ∃ X, X = Real.exp (x ^ (ε / 3)) := ⟨_, rfl⟩
  have hX0 : 0 < X := by rw [hX]; exact Real.exp_pos _
  have hXX : X * X ≤ Real.exp (x ^ ε) := by
    rw [hX, ← Real.exp_add]
    apply Real.exp_le_exp.2
    have h : x ^ ε = x ^ (2 * ε / 3) * x ^ (ε / 3) := by
      rw [← Real.rpow_add hxpos]; congr 1; ring
    rw [h]
    have := Real.rpow_nonneg hxpos.le (ε / 3)
    nlinarith
  rw [← hX] at f3 ⊢
  have hnX : n ≤ X := hn15.trans f3
  rw [le_div_iff₀ (by positivity), le_div_iff₀ hX0]
  have h : n * X ≤ Real.exp (x ^ ε) := (mul_le_mul_of_nonneg_right hnX hX0.le).trans hXX
  calc 1 * (x * n) * X = x * (n * X) := by ring
    _ ≤ x * Real.exp (x ^ ε) := by gcongr
end Formalism.LFunctionChainParameters.LChain.ModelText
