-- Prove2me | solution 1 for Formalism.LFunctionChainParameters.ThickSetMeanBounds.proposition_final_minimum
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-25T03:35:56.639607+00:00
-- url     : https://prove2.me/submissions/d33d9029-1d32-4553-8348-cae83a05b53b

import Definitions.Def_Formalism_SizeWindowBrackets_GrowthBoundGivesRiemannHypothesis
import Definitions.Def_Formalism_SizeWindowBrackets_ChainSlopeWindows_RiemannHypothesisOfPowerBound
import Definitions.Def_Formalism_SizeWindowBrackets_ChainSlopeWindows_StronglyIrreducible
import Definitions.Def_Formalism_ThickAverageLoss_ThickAverageProofs_Balance
import Definitions.Def_Formalism_ThickAverageLoss_ThickAverageProofs_ThickAverage
import Definitions.Def_Formalism_ZetaNonvanishing_GzLipschitz
import Mathlib.NumberTheory.Chebyshev
import Definitions.Def_Formalism_SizeWindowBrackets_ChainSlopeWindows_LipschitzWeightAndMinimum
import Theorems.Thm_Formalism_LFunctionChainParameters_ThickSetMeanBounds_proposition_final
import Theorems.Thm_Formalism_LFunctionChainParameters_ThickSetMeanBounds_lipschitz_weight_all
import Theorems.Thm_Formalism_LFunctionChainParameters_ThickSetMeanBounds_derivative_integral_all

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
theorem _root_.solution : RiemannHypothesisOfReducedGrowthData := by
  obtain ⟨Cd, hCd, hDer⟩ := derivative_integral_all
  refine ⟨Cd, hCd, fun C ε₁ hε₁ hIn => proposition_final C ε₁ hε₁ fun ε hε hεl => ?_⟩
  obtain ⟨x₀, hx₀⟩ := hIn ε hε hεl
  refine ⟨x₀, fun x hx => ?_⟩
  obtain ⟨H, i1, i2, i3, D, ell, N, m, TT, T2, a, w, b, b', η, X', θ, CL, Err, k, aE, hD,
    ⟨h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11, h12, h13⟩, hS, hW⟩ := hx₀ x hx
  exact ⟨H, i1, i2, i3, D, ell, N, m, TT, T2, a, w, b, b', η, X', θ, Cd, CL, Err, k, aE, hD,
    ⟨h1, h2, h3, h4, h5, h6, h7, hCd, h8, h9, h10, h11, h12, lipschitz_weight_all H D ell, hDer H D ell, h13⟩, hS, hW⟩
end Formalism.LFunctionChainParameters.ThickSetMeanBounds
