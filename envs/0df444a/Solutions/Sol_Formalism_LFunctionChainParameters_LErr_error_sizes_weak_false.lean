-- Prove2me | solution 1 for Formalism.LFunctionChainParameters.LErr.error_sizes_weak_false
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-25T17:17:26.442799+00:00
-- url     : https://prove2.me/submissions/2de743fb-6249-4167-869d-5f94d4a3a8eb

import Definitions.Def_Formalism_SizeWindowBrackets_ErrorFormsWeakWindowsFalse
import Definitions.Def_Formalism_SizeWindowBrackets_ChainSlopeWindows_SubThreeMulLogTwoLe
import Theorems.Thm_Formalism_LFunctionChainParameters_LErr_error_lower_eta
import Theorems.Thm_Formalism_LFunctionChainParameters_LErr_model_windows0

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Real
open Formalism Formalism.LFunctionChainParameters Formalism.LFunctionChainParameters.LErr
open Formalism.RankGapBounds.WeightedMeanData Formalism.LFunctionChainParameters.WeightedSlopeBounds
set_option linter.unusedVariables false
namespace Formalism.LFunctionChainParameters.LErr
theorem _root_.solution : ¬ ErrorFormsWeakWindowsFalse := by
  intro h
  have hw0 := model_windows0 1 10 (by norm_num) (by norm_num)
  have hL : LargeX (modelD 1).x (modelD 1).ε 1 (modelC 10).cHH 1 := by
    refine ⟨?_, ?_⟩
    · have := Real.log_le_self (by norm_num : (0 : ℝ) ≤ 100000)
      simpa [modelD] using this
    · norm_num [modelD, modelC, KBig]
  have h1 := h (modelD 1) (modelC 10) 3 1 1
    ⟨hw0, by norm_num [modelD], by norm_num [modelD]⟩ hL
  have h2 := error_lower_eta (modelD 1) (modelC 10) 3 1 1 hw0 (by norm_num [modelD])
  have h3 := h2.trans h1
  have e10 : (100000 : ℝ) ^ (10 : ℝ) = 100000 ^ (10 : ℕ) := by
    rw [← Real.rpow_natCast]; norm_num
  have e5 : (100000 : ℝ) ^ (((1 : ℝ) + 1 + 3) * 1) = 100000 ^ (5 : ℕ) := by
    rw [← Real.rpow_natCast]; norm_num
  simp only [modelD, modelC, CErr, ErrText, Data.nT, Real.sqrt_zero, Fintype.card_unit, e10, e5] at h3
  norm_num at h3
end Formalism.LFunctionChainParameters.LErr
