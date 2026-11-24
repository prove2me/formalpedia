-- Prove2me | solution 1 for Formalism.LFunctionChainParameters.SectionsFourToSixTransfer.exact_coefficient_to_proposition
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-24T11:06:03.114995+00:00
-- url     : https://prove2.me/submissions/d2d7c9d0-40c2-4213-84b6-7bfc23f2dc0c

import Definitions.Def_Formalism_SizeWindowBrackets_TranslateWordBoundHypotheses
import Definitions.Def_Formalism_SizeWindowBrackets_ChainSlopeWindows_LevelOfCongruence
import Definitions.Def_Formalism_SizeWindowBrackets_ChainSlopeWindows_SubThreeMulLogTwoLe
import Definitions.Def_Formalism_LogVandermondeBounds_HookGammaAmgmMultinomialBounds
import Definitions.Def_Formalism_SizeWindowBrackets_ChainSlopeWindows_SecondPriceSumWeightsUncovered
import Theorems.Thm_Formalism_LFunctionChainParameters_SectionsFourToSixTransfer_exact_coefficient_price

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
theorem _root_.solution : ExactCoeffToProp5 := by
  intro U0 W Top m f D cE c5 X bN hW hE hU hc5 hc u0 u
  have hp := exact_coefficient_price D bN hW u0
  obtain ⟨hf, hm1, hmk, hmx, hL, hv, hl0, hl1, hl2, hlg, hb⟩ := hW
  have hm1' : (1 : ℝ) ≤ (m : ℝ) := by exact_mod_cast hm1
  have hk0 : 0 < D.k := by linarith
  refine ⟨?_, hU u0 u⟩
  have h1 := hE u0 u
  have hq : 0 ≤ (m : ℝ) ^ 2 * D.L / D.k := div_nonneg (mul_nonneg (sq_nonneg _) (by linarith)) hk0.le
  have h2 : (cE + 6) * D.L ≤ c5 * D.L := mul_le_mul_of_nonneg_right hc (by linarith)
  have h3 := mul_nonneg hc5 hq
  have e : c5 * (D.L + (m : ℝ) ^ 2 * D.L / D.k) = c5 * D.L + c5 * ((m : ℝ) ^ 2 * D.L / D.k) := by ring
  rw [e]; linarith
end Formalism.LFunctionChainParameters.SectionsFourToSixTransfer
