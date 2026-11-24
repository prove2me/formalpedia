-- Prove2me | solution 1 for Formalism.LFunctionChainParameters.ThickSetMeanBounds.AN.wGz
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-24T10:30:47.343248+00:00
-- url     : https://prove2.me/submissions/c08fe177-8544-406b-8681-45b3171dfce1

import Definitions.Def_Formalism_SizeWindowBrackets_GrowthBoundGivesRiemannHypothesis
import Definitions.Def_Formalism_SizeWindowBrackets_ChainSlopeWindows_RiemannHypothesisOfPowerBound
import Definitions.Def_Formalism_SizeWindowBrackets_ChainSlopeWindows_StronglyIrreducible
import Definitions.Def_Formalism_ThickAverageLoss_ThickAverageProofs_Balance
import Definitions.Def_Formalism_ThickAverageLoss_ThickAverageProofs_ThickAverage
import Definitions.Def_Formalism_ZetaNonvanishing_GzLipschitz
import Mathlib.NumberTheory.Chebyshev
import Definitions.Def_Formalism_SizeWindowBrackets_ChainSlopeWindows_LipschitzWeightAndMinimum
import Theorems.Thm_Formalism_LFunctionChainParameters_ThickSetMeanBounds_AN_truncR

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
theorem _root_.solution (A w : ℝ) (hw : 0 < w) (M : ℕ) (hM : ⌊A / w⌋₊ ≤ M) :
    w * Gz (A / w) = ∑ n ∈ Icc 1 M, Λ n * max (A / n - w) 0 - A * Real.log (A / w)
      + (1 + Real.eulerMascheroniConstant) * A := by
  have t := truncR (fun n => Λ n) (A / w) M hM
  unfold Gz Sz
  rw [t]
  have hs : w * ∑ n ∈ Icc 1 M, Λ n * max (A / w / n - 1) 0 = ∑ n ∈ Icc 1 M, Λ n * max (A / n - w) 0 := by
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro n hn
    rw [Finset.mem_Icc] at hn
    have hn0 : (n : ℝ) ≠ 0 := by
      have : (0 : ℝ) < n := by exact_mod_cast hn.1
      exact this.ne'
    have : max (A / n - w) 0 = w * max (A / w / n - 1) 0 := by
      rw [mul_max_of_nonneg _ _ hw.le, mul_zero]
      congr 1
      field_simp
    rw [this]; ring
  rw [← hs]
  field_simp
end Formalism.LFunctionChainParameters.ThickSetMeanBounds.AN
