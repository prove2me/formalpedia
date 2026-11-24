-- Prove2me | solution 1 for Formalism.LFunctionChainParameters.ThickSetMeanBounds.AN.lip_triv
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-24T11:27:19.789181+00:00
-- url     : https://prove2.me/submissions/923c6349-154e-465d-90b9-bf4687ad39ab

import Definitions.Def_Formalism_SizeWindowBrackets_GrowthBoundGivesRiemannHypothesis
import Definitions.Def_Formalism_SizeWindowBrackets_ChainSlopeWindows_RiemannHypothesisOfPowerBound
import Definitions.Def_Formalism_SizeWindowBrackets_ChainSlopeWindows_StronglyIrreducible
import Definitions.Def_Formalism_ThickAverageLoss_ThickAverageProofs_Balance
import Definitions.Def_Formalism_ThickAverageLoss_ThickAverageProofs_ThickAverage
import Definitions.Def_Formalism_ZetaNonvanishing_GzLipschitz
import Mathlib.NumberTheory.Chebyshev
import Definitions.Def_Formalism_SizeWindowBrackets_ChainSlopeWindows_LipschitzWeightAndMinimum
import Theorems.Thm_Formalism_LFunctionChainParameters_ThickSetMeanBounds_AN_lip_triv_le

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
open Formalism.LFunctionChainParameters.ThickSetMeanBounds.AN
namespace Formalism.LFunctionChainParameters.ThickSetMeanBounds.AN
theorem _root_.solution (A w w' : ℝ) (hA : 0 < A) (hw : 0 < w) (hw' : 0 < w') :
    |w * Gz (A / w) - w' * Gz (A / w')| ≤ 3 * A / min w w' * |w - w'| := by
  rcases le_total w w' with h | h
  · rw [min_eq_left h, abs_sub_comm w w', abs_of_nonneg (by linarith : (0 : ℝ) ≤ w' - w)]
    exact lip_triv_le A w w' hA hw h
  · rw [min_eq_right h, abs_of_nonneg (by linarith : (0 : ℝ) ≤ w - w'), abs_sub_comm]
    exact lip_triv_le A w' w hA hw' h
end Formalism.LFunctionChainParameters.ThickSetMeanBounds.AN
