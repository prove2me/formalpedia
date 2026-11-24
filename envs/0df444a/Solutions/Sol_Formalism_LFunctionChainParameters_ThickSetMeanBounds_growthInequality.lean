-- Prove2me | solution 1 for Formalism.LFunctionChainParameters.ThickSetMeanBounds.growthInequality
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-24T11:39:51.903328+00:00
-- url     : https://prove2.me/submissions/69bcd7cf-cfb1-452c-b5c6-f7eb79ded612

import Definitions.Def_Formalism_SizeWindowBrackets_GrowthBoundGivesRiemannHypothesis
import Definitions.Def_Formalism_SizeWindowBrackets_ChainSlopeWindows_RiemannHypothesisOfPowerBound
import Definitions.Def_Formalism_SizeWindowBrackets_ChainSlopeWindows_StronglyIrreducible
import Definitions.Def_Formalism_ThickAverageLoss_ThickAverageProofs_Balance
import Definitions.Def_Formalism_ThickAverageLoss_ThickAverageProofs_ThickAverage
import Definitions.Def_Formalism_ZetaNonvanishing_GzLipschitz
import Mathlib.NumberTheory.Chebyshev
import Definitions.Def_Formalism_SizeWindowBrackets_ChainSlopeWindows_LipschitzWeightAndMinimum
import Theorems.Thm_Formalism_LFunctionChainParameters_ThickSetMeanBounds_proposition_finite_group

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
theorem _root_.solution {H : Type} [AddCommGroup H] [Fintype H] [DecidableEq H] : GrowthInequalityForm (H := H) := by
  intro hBal D hD ell N m TT T2 a w x ε b b' η X' θ Cd CL Err hH hS
  have hc := proposition_finite_group hBal D hD ell N m TT T2 a w x ε b b' η X' θ Cd CL Err hH
  obtain ⟨hMv, hth, hlip⟩ := hS
  have hx : 3 ≤ x := hH.1
  have hb : 0 < b := hH.2.1
  have hK : 0 ≤ (TT.card : ℝ) * m := by positivity
  have hδ : 0 ≤ delta2 T2 / 2 := by unfold delta2; positivity
  have h1 : (TT.card : ℝ) * m * b * (delta2 T2 / 2) * (Gz x - 4 * x ^ ((1 : ℝ) / 2 + ε))
      ≤ (TT.card : ℝ) * m * b * (delta2 T2 / 2) * (Gz x - 3 * x ^ ((1 : ℝ) / 2 + ε) - moveCost x Cd CL) :=
    mul_le_mul_of_nonneg_left (by linarith) (by positivity)
  have h2 : (TT.card : ℝ) * m * (2 * fPl H * (x + 1) * b * θ) ≤ (TT.card : ℝ) * m * (b * (1 / x)) := by
    apply mul_le_mul_of_nonneg_left _ hK
    calc 2 * fPl H * (x + 1) * b * θ = b * (2 * fPl H * (x + 1) * θ) := by ring
      _ ≤ b * (1 / x) := mul_le_mul_of_nonneg_left hth hb.le
  have h3 : (TT.card : ℝ) * m * (6 * fPl H * (x + 1) * (η + 1)) ≤ (TT.card : ℝ) * m * (b / x) :=
    mul_le_mul_of_nonneg_left hlip hK
  have e : 2 * (TT.card : ℝ) * m * b / x = (TT.card : ℝ) * m * (b * (1 / x)) + (TT.card : ℝ) * m * (b / x) := by
    ring
  rw [e]; linarith
end Formalism.LFunctionChainParameters.ThickSetMeanBounds
