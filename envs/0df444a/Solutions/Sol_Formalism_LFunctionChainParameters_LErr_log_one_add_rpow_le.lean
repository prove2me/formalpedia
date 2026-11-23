-- Prove2me | solution 1 for Formalism.LFunctionChainParameters.LErr.log_one_add_rpow_le
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T04:35:07.784331+00:00
-- url     : https://prove2.me/submissions/3554a19e-5fb8-4a6e-a87a-52c50d3dc8ec

import Definitions.Def_Formalism_SizeWindowBrackets_ErrorFormsWeakWindowsFalse
import Definitions.Def_Formalism_SizeWindowBrackets_ChainSlopeWindows_SubThreeMulLogTwoLe

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
theorem _root_.solution {x c y : ℝ} (hx : 1 ≤ x) (hc : 0 ≤ c) (hlog : Real.log x ≤ y)
    (hy : 1 ≤ y) : Real.log (1 + x ^ c) ≤ (1 + c) * y := by
  have hx0 : 0 < x := by linarith
  have hxH : 1 ≤ x ^ c := Real.one_le_rpow hx hc
  have hl2 : Real.log 2 ≤ 1 := by
    have := Real.log_le_sub_one_of_pos (by norm_num : (0 : ℝ) < 2)
    linarith
  calc Real.log (1 + x ^ c) ≤ Real.log (2 * x ^ c) :=
        Real.log_le_log (by linarith) (by linarith)
    _ = Real.log 2 + c * Real.log x := by
        rw [Real.log_mul (by norm_num) (by positivity), Real.log_rpow hx0]
    _ ≤ 1 * y + c * y := by
        gcongr
        linarith
    _ = (1 + c) * y := by ring
end Formalism.LFunctionChainParameters.LErr
