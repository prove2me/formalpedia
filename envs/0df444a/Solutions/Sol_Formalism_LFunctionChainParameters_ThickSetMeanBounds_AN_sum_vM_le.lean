-- Prove2me | solution 1 for Formalism.LFunctionChainParameters.ThickSetMeanBounds.AN.sum_vM_le
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-24T10:46:53.1169+00:00
-- url     : https://prove2.me/submissions/c7e8f305-721b-4275-8713-2aec79eed81f

import Definitions.Def_Formalism_SizeWindowBrackets_GrowthBoundGivesRiemannHypothesis
import Definitions.Def_Formalism_SizeWindowBrackets_ChainSlopeWindows_RiemannHypothesisOfPowerBound
import Definitions.Def_Formalism_SizeWindowBrackets_ChainSlopeWindows_StronglyIrreducible
import Definitions.Def_Formalism_ThickAverageLoss_ThickAverageProofs_Balance
import Definitions.Def_Formalism_ThickAverageLoss_ThickAverageProofs_ThickAverage
import Definitions.Def_Formalism_ZetaNonvanishing_GzLipschitz
import Mathlib.NumberTheory.Chebyshev
import Definitions.Def_Formalism_SizeWindowBrackets_ChainSlopeWindows_LipschitzWeightAndMinimum
import Theorems.Thm_Formalism_LFunctionChainParameters_ThickSetMeanBounds_AN_psi_le_three
import Theorems.Thm_Formalism_LogFactorialMertensBounds_Icc_one_eq_Ioc


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
theorem _root_.solution {Y : ℝ} (hY : 0 ≤ Y) : ∑ n ∈ Icc 1 ⌊Y⌋₊, Λ n ≤ 3 * Y := by
  rw [Formalism.LogFactorialMertensBounds.Icc_one_eq_Ioc]; exact psi_le_three hY
end Formalism.LFunctionChainParameters.ThickSetMeanBounds.AN
