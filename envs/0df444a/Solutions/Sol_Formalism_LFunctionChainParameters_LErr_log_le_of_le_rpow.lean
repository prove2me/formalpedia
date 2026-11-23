-- Prove2me | solution 1 for Formalism.LFunctionChainParameters.LErr.log_le_of_le_rpow
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T04:35:07.786999+00:00
-- url     : https://prove2.me/submissions/922ef832-70be-45f6-96b1-259eee919975

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
theorem _root_.solution {x k e y : ℝ} (hx : 1 ≤ x) (he : 0 ≤ e) (hk : 0 < k) (hkx : k ≤ x ^ e)
    (hlog : Real.log x ≤ y) (hy : 1 ≤ y) : Real.log k ≤ (1 + e) * y := by
  have hx0 : 0 < x := by linarith
  calc Real.log k ≤ Real.log (x ^ e) := Real.log_le_log hk hkx
    _ = e * Real.log x := Real.log_rpow hx0 _
    _ ≤ e * y := by gcongr
    _ ≤ (1 + e) * y := by linarith
end Formalism.LFunctionChainParameters.LErr
