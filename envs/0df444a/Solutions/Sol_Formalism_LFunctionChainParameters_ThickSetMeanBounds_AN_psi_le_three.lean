-- Prove2me | solution 1 for Formalism.LFunctionChainParameters.ThickSetMeanBounds.AN.psi_le_three
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-24T10:30:45.612215+00:00
-- url     : https://prove2.me/submissions/c53a3deb-fdcb-4399-85c6-047dc3d3d10c

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
open Formalism.LFunctionChainParameters.ThickSetMeanBounds.AN
namespace Formalism.LFunctionChainParameters.ThickSetMeanBounds.AN
theorem _root_.solution {y : ℝ} (hy : 0 ≤ y) : Chebyshev.psi y ≤ 3 * y := by
  by_cases h1 : y < 1
  · rw [Chebyshev.psi_eq_zero_of_lt_two (by linarith)]; linarith
  · have h1' : 1 ≤ y := not_lt.1 h1
    have hp := Chebyshev.psi_le h1'
    have hs0 : 0 < Real.sqrt y := Real.sqrt_pos.2 (by linarith)
    have hss : Real.sqrt y * Real.sqrt y = y := Real.mul_self_sqrt hy
    have hlog : Real.log y = 2 * Real.log (Real.sqrt y) := by
      rw [← hss, Real.log_mul hs0.ne' hs0.ne', hss]; ring
    have hu : Real.log (Real.sqrt y) ≤ Real.sqrt y * Real.exp (-1) := by
      have := Real.add_one_le_exp (Real.log (Real.sqrt y) - 1)
      rw [sub_eq_add_neg, Real.exp_add, Real.exp_log hs0] at this
      linarith
    have he := Real.exp_neg_one_lt_d9
    have hl2 := Real.log_two_lt_d9
    have hl4 : Real.log 4 = 2 * Real.log 2 := by
      rw [show (4 : ℝ) = 2 ^ 2 by norm_num, Real.log_pow]; norm_num
    have h2 : 2 * Real.sqrt y * Real.log y ≤ 4 * Real.exp (-1) * y := by
      rw [hlog]
      have : Real.sqrt y * Real.log (Real.sqrt y) ≤ Real.sqrt y * (Real.sqrt y * Real.exp (-1)) :=
        mul_le_mul_of_nonneg_left hu hs0.le
      nlinarith
    nlinarith
end Formalism.LFunctionChainParameters.ThickSetMeanBounds.AN
