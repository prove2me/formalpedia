-- Prove2me | solution 1 for Formalism.LFunctionChainParameters.SectionsFourToSixTransfer.bernoulli_level
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-24T10:30:53.588999+00:00
-- url     : https://prove2.me/submissions/2ac9e363-7a05-4ddb-b864-7a56701b1896

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
theorem _root_.solution (f : ℕ) {T : ℝ} (hT : 2 ≤ T) :
    1 - (f : ℝ) / (T - 1) ≤ (1 - 1 / (T - 1)) ^ f := by
  have hy : 0 < T - 1 := by linarith
  have h1 : 1 / (T - 1) ≤ 1 := by rw [div_le_one hy]; linarith
  have h := one_add_mul_le_pow (a := -(1 / (T - 1))) (by linarith) f
  have e1 : 1 + (f : ℝ) * -(1 / (T - 1)) = 1 - (f : ℝ) / (T - 1) := by ring
  have e2 : 1 + -(1 / (T - 1)) = 1 - 1 / (T - 1) := by ring
  rw [e1, e2] at h
  exact h
end Formalism.LFunctionChainParameters.SectionsFourToSixTransfer
