-- Prove2me | solution 1 for Formalism.LFunctionChainParameters.LErr.inv_one_sub_le_two
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T04:35:07.865795+00:00
-- url     : https://prove2.me/submissions/9fb1f38e-0cfd-4300-89c4-bf2426ba7a2c

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
theorem _root_.solution {d : ℝ} (hd : d ≤ 1 / 2) : 0 ≤ (1 - d)⁻¹ ∧ (1 - d)⁻¹ ≤ 2 := by
  have hd12 : (1 : ℝ) / 2 ≤ 1 - d := by linarith
  refine ⟨inv_nonneg.2 (by linarith), ?_⟩
  have := inv_anti₀ (by norm_num : (0 : ℝ) < 1 / 2) hd12
  simpa using this
end Formalism.LFunctionChainParameters.LErr
