-- Prove2me | solution 1 for Formalism.LFunctionChainParameters.SectionsFourToSixTransfer.pow_of_log
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-24T10:30:42.57201+00:00
-- url     : https://prove2.me/submissions/25057062-06fd-4070-8375-32c99816acf3

import Definitions.Def_Formalism_SizeWindowBrackets_TranslateWordBoundHypotheses
import Definitions.Def_Formalism_SizeWindowBrackets_ChainSlopeWindows_LevelOfCongruence
import Definitions.Def_Formalism_SizeWindowBrackets_ChainSlopeWindows_SubThreeMulLogTwoLe
import Definitions.Def_Formalism_LogVandermondeBounds_HookGammaAmgmMultinomialBounds
import Definitions.Def_Formalism_SizeWindowBrackets_ChainSlopeWindows_SecondPriceSumWeightsUncovered

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Real
open Formalism Formalism.LFunctionChainParameters Formalism.LFunctionChainParameters.SectionsFourToSixTransfer
open Formalism.RankGapBounds.WeightedMeanData Formalism.LFunctionChainParameters.WeightedSlopeBounds Formalism.LFunctionChainParameters.LErr Formalism.LFunctionChainParameters.LatticeToWeightTransfer
namespace Formalism.LFunctionChainParameters.SectionsFourToSixTransfer
theorem _root_.solution : PowOfLog := by
  intro mR b T hb hT
  have hp : 0 < b ^ (mR / 2) := Real.rpow_pos_of_pos hb _
  rw [← Real.log_le_log_iff hp hT, Real.log_rpow hb]
  constructor <;> intro h <;> linarith
end Formalism.LFunctionChainParameters.SectionsFourToSixTransfer
