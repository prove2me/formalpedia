-- Prove2me | solution 1 for Formalism.LFunctionChainParameters.ThickSetMeanBounds.AN.lip_char
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-24T11:29:14.324973+00:00
-- url     : https://prove2.me/submissions/f2d8afd4-fdd2-4a58-9c88-8b5db9aada08

import Definitions.Def_Formalism_SizeWindowBrackets_GrowthBoundGivesRiemannHypothesis
import Definitions.Def_Formalism_SizeWindowBrackets_ChainSlopeWindows_RiemannHypothesisOfPowerBound
import Definitions.Def_Formalism_SizeWindowBrackets_ChainSlopeWindows_StronglyIrreducible
import Definitions.Def_Formalism_ThickAverageLoss_ThickAverageProofs_Balance
import Definitions.Def_Formalism_ThickAverageLoss_ThickAverageProofs_ThickAverage
import Definitions.Def_Formalism_ZetaNonvanishing_GzLipschitz
import Mathlib.NumberTheory.Chebyshev
import Definitions.Def_Formalism_SizeWindowBrackets_ChainSlopeWindows_LipschitzWeightAndMinimum
import Theorems.Thm_Formalism_LFunctionChainParameters_ThickSetMeanBounds_AN_sum_vM_le
import Theorems.Thm_Formalism_LFunctionChainParameters_ThickSetMeanBounds_AN_norm_coef_le
import Theorems.Thm_Formalism_LFunctionChainParameters_ThickSetMeanBounds_AN_wG_char
import Theorems.Thm_Formalism_LFunctionChainParameters_ThickSetMeanBounds_AN_floor_div_le

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
variable {H : Type} [AddCommGroup H] [Fintype H] [DecidableEq H]
namespace Formalism.LFunctionChainParameters.ThickSetMeanBounds.AN
theorem _root_.solution (D : ArithData H) (ell : AddChar (E0 × H) ℂ → ℂ) (ψ : AddChar (E0 × H) ℂ) (hψ : ψ ≠ 0)
    (A w w' : ℝ) (hA : 0 < A) (hw : 0 < w) (hw' : 0 < w') :
    ‖(w : ℂ) * GPsi D ell ψ (A / w) - (w' : ℂ) * GPsi D ell ψ (A / w')‖ ≤ 3 * A / min w w' * |w - w'| := by
  have hμ : 0 < min w w' := lt_min hw hw'
  rw [wG_char D ell ψ hψ A w hw _ (floor_div_le hA.le hμ (min_le_left _ _)),
    wG_char D ell ψ hψ A w' hw' _ (floor_div_le hA.le hμ (min_le_right _ _)), add_sub_add_right_eq_sub,
    ← Finset.sum_sub_distrib]
  refine le_trans (norm_sum_le _ _) ?_
  have hterm : ∀ n ∈ Icc 1 ⌊A / min w w'⌋₊,
      ‖(Λ n : ℂ) * primVal D ψ n * ((max (A / n - w) 0 : ℝ) : ℂ)
        - (Λ n : ℂ) * primVal D ψ n * ((max (A / n - w') 0 : ℝ) : ℂ)‖ ≤ Λ n * |w - w'| := by
    intro n _
    rw [← mul_sub, ← Complex.ofReal_sub, norm_mul, Complex.norm_real, Real.norm_eq_abs]
    have ha : |max (A / n - w) 0 - max (A / n - w') 0| ≤ |w - w'| := by
      refine le_trans (abs_max_sub_max_le_abs _ _ _) ?_
      have : A / n - w - (A / n - w') = -(w - w') := by ring
      rw [this, abs_neg]
    exact mul_le_mul (norm_coef_le D ψ n) ha (abs_nonneg _) ArithmeticFunction.vonMangoldt_nonneg
  refine le_trans (Finset.sum_le_sum hterm) ?_
  rw [← Finset.sum_mul]
  have := sum_vM_le (Y := A / min w w') (by positivity)
  calc (∑ n ∈ Icc 1 ⌊A / min w w'⌋₊, Λ n) * |w - w'| ≤ (3 * (A / min w w')) * |w - w'| :=
        mul_le_mul_of_nonneg_right this (abs_nonneg _)
    _ = 3 * A / min w w' * |w - w'| := by ring
end Formalism.LFunctionChainParameters.ThickSetMeanBounds.AN
