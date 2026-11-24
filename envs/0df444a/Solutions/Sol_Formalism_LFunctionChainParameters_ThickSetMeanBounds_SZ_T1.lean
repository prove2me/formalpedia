-- Prove2me | solution 1 for Formalism.LFunctionChainParameters.ThickSetMeanBounds.SZ.T1
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-24T10:30:52.15445+00:00
-- url     : https://prove2.me/submissions/3117daed-b9ed-45aa-86f6-be6d14ca67bd

import Definitions.Def_Formalism_SizeWindowBrackets_GrowthBoundGivesRiemannHypothesis
import Definitions.Def_Formalism_SizeWindowBrackets_ChainSlopeWindows_RiemannHypothesisOfPowerBound
import Definitions.Def_Formalism_SizeWindowBrackets_ChainSlopeWindows_StronglyIrreducible
import Definitions.Def_Formalism_ThickAverageLoss_ThickAverageProofs_Balance
import Definitions.Def_Formalism_ThickAverageLoss_ThickAverageProofs_ThickAverage
import Definitions.Def_Formalism_ZetaNonvanishing_GzLipschitz
import Mathlib.NumberTheory.Chebyshev
import Definitions.Def_Formalism_SizeWindowBrackets_ChainSlopeWindows_LipschitzWeightAndMinimum

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Finset ArithmeticFunction
noncomputable section
open Formalism Formalism.LFunctionChainParameters Formalism.LFunctionChainParameters.ThickSetMeanBounds
open Formalism Formalism.D5 Formalism.LFunctionChainParameters.characterSumData
open Formalism.LFunctionChainParameters.ThickSetMeanBounds.SZ
namespace Formalism.LFunctionChainParameters.ThickSetMeanBounds.SZ
theorem _root_.solution {x X Y m nT aE b : ℝ} (hxX : x ≤ X * m) (hXY : X ≤ Y) (hnT0 : 0 ≤ nT) (hm0 : 0 ≤ m) (hb : 0 ≤ b)
    (haE : aE ≤ 2 * x * b) : nT * aE ≤ 2 * Y * (nT * m * b) := by
  have h1 : nT * aE ≤ nT * (2 * x * b) := mul_le_mul_of_nonneg_left haE hnT0
  have h2 : 2 * x * b ≤ 2 * (Y * m) * b := by
    have : x ≤ Y * m := le_trans hxX (mul_le_mul_of_nonneg_right hXY hm0)
    nlinarith
  have h3 : nT * (2 * x * b) ≤ nT * (2 * (Y * m) * b) := mul_le_mul_of_nonneg_left h2 hnT0
  calc nT * aE ≤ nT * (2 * (Y * m) * b) := le_trans h1 h3
    _ = 2 * Y * (nT * m * b) := by ring
end Formalism.LFunctionChainParameters.ThickSetMeanBounds.SZ
