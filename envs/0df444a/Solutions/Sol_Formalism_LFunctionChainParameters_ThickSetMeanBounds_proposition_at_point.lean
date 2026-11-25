-- Prove2me | solution 1 for Formalism.LFunctionChainParameters.ThickSetMeanBounds.proposition_at_point
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-25T03:24:23.766641+00:00
-- url     : https://prove2.me/submissions/c66d96ff-41c1-4ff0-b163-f07ceed75f18

import Definitions.Def_Formalism_SizeWindowBrackets_GrowthBoundGivesRiemannHypothesis
import Definitions.Def_Formalism_SizeWindowBrackets_ChainSlopeWindows_RiemannHypothesisOfPowerBound
import Definitions.Def_Formalism_SizeWindowBrackets_ChainSlopeWindows_StronglyIrreducible
import Definitions.Def_Formalism_ThickAverageLoss_ThickAverageProofs_Balance
import Definitions.Def_Formalism_ThickAverageLoss_ThickAverageProofs_ThickAverage
import Definitions.Def_Formalism_ZetaNonvanishing_GzLipschitz
import Mathlib.NumberTheory.Chebyshev
import Definitions.Def_Formalism_SizeWindowBrackets_ChainSlopeWindows_LipschitzWeightAndMinimum
import Theorems.Thm_Formalism_LFunctionChainParameters_ThickSetMeanBounds_proposition_size_bound
import Theorems.Thm_Formalism_LFunctionChainParameters_ThickSetMeanBounds_growthInequality
import Theorems.Thm_Formalism_LFunctionChainParameters_characterSumData_colour_balance


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
theorem _root_.solution : GrowthBoundAtPoint := by
  intro C ε x hI
  obtain ⟨H, i1, i2, i3, D, ell, N, m, TT, T2, a, w, b, b', η, X', θ, Cd, CL, Err, k, aE, hD, hH, hS, hW⟩ := hI
  have ht := growthInequality (Formalism.LFunctionChainParameters.characterSumData.colour_balance (H := H)) D hD ell N m TT T2 a w x ε b b' η X' θ Cd CL
    Err hH hS
  exact proposition_size_bound C ε x (Fintype.card H) TT.card T2.card m b k aE Err (Gz x) hW ht
end Formalism.LFunctionChainParameters.ThickSetMeanBounds
