-- Prove2me | solution 1 for Formalism.LFunctionChainParameters.ThickSetMeanBounds.AN.norm_cosetMean_le
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-24T10:30:44.762218+00:00
-- url     : https://prove2.me/submissions/650454b3-9149-4209-a83d-3edb79ec21ca

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
variable {H : Type} [AddCommGroup H] [Fintype H] [DecidableEq H]
namespace Formalism.LFunctionChainParameters.ThickSetMeanBounds.AN
theorem _root_.solution (I : AddSubgroup (E0 × H)) (h : E0 × H) (ψ : AddChar (E0 × H) ℂ) :
    ‖cosetMean I h ψ‖ ≤ 1 := by
  classical
  unfold cosetMean
  rw [norm_div]
  have hc : (0 : ℝ) < ((univ.filter (fun x => x ∈ I)).card : ℝ) := by
    have h0 : (0 : E0 × H) ∈ univ.filter (fun x => x ∈ I) := by simp
    exact_mod_cast Finset.card_pos.2 ⟨0, h0⟩
  have hn : ‖(((univ.filter (fun x => x ∈ I)).card : ℕ) : ℂ)‖ = ((univ.filter (fun x => x ∈ I)).card : ℝ) := by
    simp
  rw [hn, div_le_one hc]
  refine le_trans (norm_sum_le _ _) ?_
  simp [AddChar.norm_apply]
end Formalism.LFunctionChainParameters.ThickSetMeanBounds.AN
