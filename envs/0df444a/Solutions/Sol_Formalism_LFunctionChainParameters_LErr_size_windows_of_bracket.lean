-- Prove2me | solution 1 for Formalism.LFunctionChainParameters.LErr.size_windows_of_bracket
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-25T17:17:34.090919+00:00
-- url     : https://prove2.me/submissions/6096dda0-865c-43a5-8e00-5a763d4b9e9b

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
open Formalism Formalism.D5 Formalism.LFunctionChainParameters.characterSumData Formalism.LFunctionChainParameters.ThickSetMeanBounds
namespace Formalism.LFunctionChainParameters.LErr
theorem _root_.solution : SizeWindowsOfBracket := by
  intro C ε x n nT nT2 m b k aE Err0 h
  obtain ⟨h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11, h12, h13, h14, -, h16⟩ := h
  exact ⟨h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11, h12, h13, h14, le_refl _, h16⟩
end Formalism.LFunctionChainParameters.LErr
