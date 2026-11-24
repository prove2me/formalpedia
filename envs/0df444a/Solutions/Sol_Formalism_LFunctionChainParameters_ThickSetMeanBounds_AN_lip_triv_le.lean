-- Prove2me | solution 1 for Formalism.LFunctionChainParameters.ThickSetMeanBounds.AN.lip_triv_le
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-24T11:05:59.991089+00:00
-- url     : https://prove2.me/submissions/5a9e0faf-9b1e-443a-beff-5bb745971660

import Definitions.Def_Formalism_SizeWindowBrackets_GrowthBoundGivesRiemannHypothesis
import Definitions.Def_Formalism_SizeWindowBrackets_ChainSlopeWindows_RiemannHypothesisOfPowerBound
import Definitions.Def_Formalism_SizeWindowBrackets_ChainSlopeWindows_StronglyIrreducible
import Definitions.Def_Formalism_ThickAverageLoss_ThickAverageProofs_Balance
import Definitions.Def_Formalism_ThickAverageLoss_ThickAverageProofs_ThickAverage
import Definitions.Def_Formalism_ZetaNonvanishing_GzLipschitz
import Mathlib.NumberTheory.Chebyshev
import Definitions.Def_Formalism_SizeWindowBrackets_ChainSlopeWindows_LipschitzWeightAndMinimum
import Theorems.Thm_Formalism_LFunctionChainParameters_ThickSetMeanBounds_AN_sum_vM_le
import Theorems.Thm_Formalism_LFunctionChainParameters_ThickSetMeanBounds_AN_floor_div_le
import Theorems.Thm_Formalism_LFunctionChainParameters_ThickSetMeanBounds_AN_wGz

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
theorem _root_.solution (A w w' : ℝ) (hA : 0 < A) (hw : 0 < w) (hww : w ≤ w') :
    |w * Gz (A / w) - w' * Gz (A / w')| ≤ 3 * A / w * (w' - w) := by
  have hw' : 0 < w' := lt_of_lt_of_le hw hww
  rw [wGz A w hw ⌊A / w⌋₊ le_rfl, wGz A w' hw' ⌊A / w⌋₊ (floor_div_le hA.le hw hww)]
  have hS0 : 0 ≤ ∑ n ∈ Icc 1 ⌊A / w⌋₊, Λ n * max (A / n - w) 0 - ∑ n ∈ Icc 1 ⌊A / w⌋₊, Λ n * max (A / n - w') 0 := by
    rw [← Finset.sum_sub_distrib]
    apply Finset.sum_nonneg
    intro n _
    rw [← mul_sub]
    apply mul_nonneg ArithmeticFunction.vonMangoldt_nonneg
    have : max (A / n - w') 0 ≤ max (A / n - w) 0 := max_le_max (by linarith) le_rfl
    linarith
  have hS1 : ∑ n ∈ Icc 1 ⌊A / w⌋₊, Λ n * max (A / n - w) 0 - ∑ n ∈ Icc 1 ⌊A / w⌋₊, Λ n * max (A / n - w') 0
      ≤ 3 * A / w * (w' - w) := by
    rw [← Finset.sum_sub_distrib]
    have hterm : ∀ n ∈ Icc 1 ⌊A / w⌋₊, Λ n * max (A / n - w) 0 - Λ n * max (A / n - w') 0 ≤ Λ n * (w' - w) := by
      intro n _
      rw [← mul_sub]
      apply mul_le_mul_of_nonneg_left _ ArithmeticFunction.vonMangoldt_nonneg
      have h := abs_max_sub_max_le_abs (A / n - w) (A / n - w') 0
      have e : A / n - w - (A / n - w') = w' - w := by ring
      rw [e, abs_of_nonneg (by linarith : (0 : ℝ) ≤ w' - w)] at h
      exact le_trans (le_abs_self _) h
    refine le_trans (Finset.sum_le_sum hterm) ?_
    rw [← Finset.sum_mul]
    have := sum_vM_le (Y := A / w) (by positivity)
    calc (∑ n ∈ Icc 1 ⌊A / w⌋₊, Λ n) * (w' - w) ≤ (3 * (A / w)) * (w' - w) :=
          mul_le_mul_of_nonneg_right this (by linarith)
      _ = 3 * A / w * (w' - w) := by ring
  have hL : A * Real.log (A / w) - A * Real.log (A / w') = A * Real.log (w' / w) := by
    rw [Real.log_div hA.ne' hw.ne', Real.log_div hA.ne' hw'.ne', Real.log_div hw'.ne' hw.ne']; ring
  have hL0 : 0 ≤ A * Real.log (w' / w) :=
    mul_nonneg hA.le (Real.log_nonneg ((one_le_div hw).2 hww))
  have hL1 : A * Real.log (w' / w) ≤ 3 * A / w * (w' - w) := by
    have h1 := Real.log_le_sub_one_of_pos (div_pos hw' hw)
    have h2 : A * Real.log (w' / w) ≤ A * (w' / w - 1) := mul_le_mul_of_nonneg_left h1 hA.le
    have h3 : A * (w' / w - 1) = A / w * (w' - w) := by field_simp
    have h4 : A / w * (w' - w) ≤ 3 * A / w * (w' - w) := by
      apply mul_le_mul_of_nonneg_right _ (by linarith)
      rw [mul_div_assoc]
      have : 0 ≤ A / w := by positivity
      linarith
    linarith
  rw [abs_le]
  constructor <;> linarith
end Formalism.LFunctionChainParameters.ThickSetMeanBounds.AN
