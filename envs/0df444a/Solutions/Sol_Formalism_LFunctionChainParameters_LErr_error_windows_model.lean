-- Prove2me | solution 1 for Formalism.LFunctionChainParameters.LErr.error_windows_model
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-25T17:17:30.667938+00:00
-- url     : https://prove2.me/submissions/0f687930-68e9-4223-ae1d-86d15cc66118

import Definitions.Def_Formalism_SizeWindowBrackets_ErrorFormsWeakWindowsFalse
import Definitions.Def_Formalism_SizeWindowBrackets_ChainSlopeWindows_SubThreeMulLogTwoLe
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
theorem _root_.solution : ErrWindowsModel := by
  refine ⟨modelD (1 / 100000), modelC 1, 3, 1, 1,
    ⟨model_windows0 _ _ (by norm_num) (by norm_num), ?_⟩, ⟨?_, ?_⟩, by norm_num [modelD],
    rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩
  · norm_num [modelD, modelC, Data.nT]
  · have := Real.log_le_self (by norm_num : (0 : ℝ) ≤ 100000)
    simpa [modelD] using this
  · norm_num [modelD, modelC, KBig]
end Formalism.LFunctionChainParameters.LErr
