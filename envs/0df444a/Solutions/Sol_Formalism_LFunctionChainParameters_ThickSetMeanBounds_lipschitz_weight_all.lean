-- Prove2me | solution 1 for Formalism.LFunctionChainParameters.ThickSetMeanBounds.lipschitz_weight_all
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-24T11:36:48.206364+00:00
-- url     : https://prove2.me/submissions/15d567bf-5689-48b1-9968-fd458ac1d6cb

import Definitions.Def_Formalism_SizeWindowBrackets_GrowthBoundGivesRiemannHypothesis
import Definitions.Def_Formalism_SizeWindowBrackets_ChainSlopeWindows_RiemannHypothesisOfPowerBound
import Definitions.Def_Formalism_SizeWindowBrackets_ChainSlopeWindows_StronglyIrreducible
import Definitions.Def_Formalism_ThickAverageLoss_ThickAverageProofs_Balance
import Definitions.Def_Formalism_ThickAverageLoss_ThickAverageProofs_ThickAverage
import Definitions.Def_Formalism_ZetaNonvanishing_GzLipschitz
import Mathlib.NumberTheory.Chebyshev
import Definitions.Def_Formalism_SizeWindowBrackets_ChainSlopeWindows_LipschitzWeightAndMinimum
import Theorems.Thm_Formalism_LFunctionChainParameters_ThickSetMeanBounds_AN_lip_char
import Theorems.Thm_Formalism_LFunctionChainParameters_ThickSetMeanBounds_AN_lip_triv

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
theorem _root_.solution : LipWAll := by
  intro H _ _ _ D ell ψ A w w' hA hw hw'
  by_cases hψ : ψ = 0
  · subst hψ
    have e : ∀ y : ℝ, GPsi D ell 0 y = ((Gz y : ℝ) : ℂ) := fun y => by simp [GPsi]
    rw [e, e, ← Complex.ofReal_mul, ← Complex.ofReal_mul, ← Complex.ofReal_sub, Complex.norm_real, Real.norm_eq_abs]
    exact AN.lip_triv A w w' hA hw hw'
  · exact AN.lip_char D ell ψ hψ A w w' hA hw hw'
end Formalism.LFunctionChainParameters.ThickSetMeanBounds
