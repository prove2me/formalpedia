-- Prove2me | solution 1 for Formalism.LFunctionChainParameters.SectionsFourToSixTransfer.logT_bounds
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-24T10:30:40.412971+00:00
-- url     : https://prove2.me/submissions/898221a0-eac8-44dd-97e6-0d4eee1cdae9

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
theorem _root_.solution {X Gam y T : ℝ} (hX : 0 < X) (hG : 1 ≤ Gam) (hy : 0 < y)
    (h1 : X * Gam ^ (-(2 / y)) ≤ T) (h2 : T ≤ X * Gam ^ (-(2 / y)) * (1 + 1 / y)) :
    Real.log X - 2 * Real.log Gam / y ≤ Real.log T ∧
    Real.log T ≤ Real.log X - 2 * Real.log Gam / y + 1 / y := by
  have hG0 : 0 < Gam := by linarith
  have hp : 0 < Gam ^ (-(2 / y)) := Real.rpow_pos_of_pos hG0 _
  have hS : 0 < X * Gam ^ (-(2 / y)) := mul_pos hX hp
  have hT : 0 < T := lt_of_lt_of_le hS h1
  have hy1 : 0 < 1 + 1 / y := by positivity
  have e : Real.log (X * Gam ^ (-(2 / y))) = Real.log X - 2 * Real.log Gam / y := by
    rw [Real.log_mul hX.ne' hp.ne', Real.log_rpow hG0]; ring
  constructor
  · rw [← e]; exact Real.log_le_log hS h1
  · have h3 := Real.log_le_log hT h2
    rw [Real.log_mul hS.ne' hy1.ne', e] at h3
    have h4 := Real.log_le_sub_one_of_pos hy1
    linarith
end Formalism.LFunctionChainParameters.SectionsFourToSixTransfer
