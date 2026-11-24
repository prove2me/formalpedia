-- Prove2me | solution 1 for Formalism.LFunctionChainParameters.LErr.error_sizes_eventually
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-24T11:05:24.452566+00:00
-- url     : https://prove2.me/submissions/4fae2962-cc3c-4c4f-b00c-d4a911822293

import Definitions.Def_Formalism_SizeWindowBrackets_ErrorFormsWeakWindowsFalse
import Definitions.Def_Formalism_SizeWindowBrackets_ChainSlopeWindows_SubThreeMulLogTwoLe
import Theorems.Thm_Formalism_LFunctionChainParameters_LErr_error_sizes
import Theorems.Thm_Formalism_LFunctionChainParameters_LErr_large_x_eventually

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
theorem _root_.solution : ErrorFormsEventual := by
  intro ε K cHH eK hε
  obtain ⟨x0, hx0⟩ := large_x_eventually ε K cHH eK hε
  refine ⟨x0, ?_⟩
  intro U0 _ W _ _ Top _ m f D C Xpp h1 h2 hx hW
  refine error_sizes D C Xpp eK K hW ?_
  rw [h1, h2]
  exact hx0 _ hx
end Formalism.LFunctionChainParameters.LErr
