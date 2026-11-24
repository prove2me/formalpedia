-- Prove2me | solution 1 for Formalism.LFunctionChainParameters.ThickSetMeanBounds.derivative_integral_all
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-24T11:57:45.901795+00:00
-- url     : https://prove2.me/submissions/2f71e54a-dc00-4bf8-bfb9-8baeaffbf1c1

import Definitions.Def_Formalism_SizeWindowBrackets_GrowthBoundGivesRiemannHypothesis
import Definitions.Def_Formalism_SizeWindowBrackets_ChainSlopeWindows_RiemannHypothesisOfPowerBound
import Definitions.Def_Formalism_SizeWindowBrackets_ChainSlopeWindows_StronglyIrreducible
import Definitions.Def_Formalism_ThickAverageLoss_ThickAverageProofs_Balance
import Definitions.Def_Formalism_ThickAverageLoss_ThickAverageProofs_ThickAverage
import Definitions.Def_Formalism_ZetaNonvanishing_GzLipschitz
import Mathlib.NumberTheory.Chebyshev
import Definitions.Def_Formalism_SizeWindowBrackets_ChainSlopeWindows_LipschitzWeightAndMinimum
import Theorems.Thm_Formalism_LFunctionChainParameters_ThickSetMeanBounds_AN_deriv_char
import Theorems.Thm_Formalism_zetaPrimeSumErrorLipschitz


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
namespace Formalism.LFunctionChainParameters.ThickSetMeanBounds
theorem _root_.solution : DerivIntAll := by
  obtain ⟨K, hK⟩ := Formalism.zetaPrimeSumErrorLipschitz
  have hl4 : 0 ≤ Real.log 4 := Real.log_nonneg (by norm_num)
  refine ⟨|K| + (Real.log 4 + 4), by positivity, ?_⟩
  intro H _ _ _ D ell
  constructor
  · intro ψ hψ y z hy hz
    refine le_trans (AN.deriv_char D ell ψ hψ y z hy hz) ?_
    apply mul_le_mul_of_nonneg_left _ (abs_nonneg _)
    have := abs_nonneg K
    linarith
  · intro y z hy hz
    refine le_trans (hK y z (by linarith) (by linarith)).2 ?_
    apply mul_le_mul_of_nonneg_right _ (abs_nonneg _)
    have := le_abs_self K
    linarith
end Formalism.LFunctionChainParameters.ThickSetMeanBounds
