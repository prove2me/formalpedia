-- Prove2me | solution 1 for Formalism.LFunctionChainParameters.LChain.ModelText.cost1
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-24T10:29:31.38083+00:00
-- url     : https://prove2.me/submissions/cd78f5f6-2f08-44ed-af3a-f70a8b26fb4c

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
theorem _root_.solution {x ε n : ℝ} (h48 : 48 ≤ x) (_hn0 : 0 < n) (hn15 : n ≤ x ^ (15 : ℝ))
    (f1 : x ^ (18 : ℝ) ≤ Real.exp (x ^ (ε / 8))) : 2 * (2 * n) * (x + 1) * thTx x ε ≤ 1 / x := by
  have hxpos : 0 < x := by linarith
  have hp15 : 0 < x ^ (15 : ℝ) := Real.rpow_pos_of_pos hxpos _
  unfold thTx
  rw [Real.exp_neg, le_div_iff₀ hxpos]
  have hE : 0 < Real.exp (x ^ (ε / 8)) := Real.exp_pos _
  have h1 : 2 * (2 * n) * (x + 1) * x ≤ Real.exp (x ^ (ε / 8)) := by
    refine le_trans ?_ f1
    rw [h18 hxpos]
    have h2 : 2 * (2 * n) * (x + 1) * x ≤ 2 * (2 * x ^ (15 : ℝ)) * (x + 1) * x := by gcongr
    have h3 : 2 * (2 * x ^ (15 : ℝ)) * (x + 1) * x ≤ x ^ (15 : ℝ) * x * x * x := by
      have h4 : 4 * (x + 1) ≤ x * x := by nlinarith
      have h5 : 0 < x ^ (15 : ℝ) * x := by positivity
      calc 2 * (2 * x ^ (15 : ℝ)) * (x + 1) * x = (x ^ (15 : ℝ) * x) * (4 * (x + 1)) := by ring
        _ ≤ (x ^ (15 : ℝ) * x) * (x * x) := by gcongr
        _ = x ^ (15 : ℝ) * x * x * x := by ring
    linarith
  calc 2 * (2 * n) * (x + 1) * (Real.exp (x ^ (ε / 8)))⁻¹ * x
      = (2 * (2 * n) * (x + 1) * x) * (Real.exp (x ^ (ε / 8)))⁻¹ := by ring
    _ ≤ Real.exp (x ^ (ε / 8)) * (Real.exp (x ^ (ε / 8)))⁻¹ := by gcongr
    _ = 1 := mul_inv_cancel₀ hE.ne'
end Formalism.LFunctionChainParameters.LChain.ModelText
