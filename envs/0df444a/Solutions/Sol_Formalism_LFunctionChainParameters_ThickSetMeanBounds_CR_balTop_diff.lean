-- Prove2me | solution 1 for Formalism.LFunctionChainParameters.ThickSetMeanBounds.CR.balTop_diff
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-24T11:06:04.575246+00:00
-- url     : https://prove2.me/submissions/1739e6e8-e6ee-4b32-9187-696792a55742

import Definitions.Def_Formalism_SizeWindowBrackets_GrowthBoundGivesRiemannHypothesis
import Definitions.Def_Formalism_SizeWindowBrackets_ChainSlopeWindows_RiemannHypothesisOfPowerBound
import Definitions.Def_Formalism_SizeWindowBrackets_ChainSlopeWindows_StronglyIrreducible
import Definitions.Def_Formalism_ThickAverageLoss_ThickAverageProofs_Balance
import Definitions.Def_Formalism_ThickAverageLoss_ThickAverageProofs_ThickAverage
import Definitions.Def_Formalism_ZetaNonvanishing_GzLipschitz
import Mathlib.NumberTheory.Chebyshev
import Definitions.Def_Formalism_SizeWindowBrackets_ChainSlopeWindows_LipschitzWeightAndMinimum
import Theorems.Thm_Formalism_LFunctionChainParameters_ThickSetMeanBounds_CR_card_S_le
import Theorems.Thm_Formalism_LFunctionChainParameters_ThickSetMeanBounds_CR_norm_avg_le

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
open Formalism.LFunctionChainParameters.ThickSetMeanBounds.CR
variable {H : Type} [AddCommGroup H] [Fintype H] [DecidableEq H]
namespace Formalism.LFunctionChainParameters.ThickSetMeanBounds.CR
theorem _root_.solution (Hs : CycHost H) (a : ℝ) (t : H) (w w' : E0 × H → ℝ) (K : ℝ) (hK0 : 0 ≤ K)
    (hK : ∀ g, ¬ InPhi (g + topPl t) → ∀ ψ : AddChar (E0 × H) ℂ,
      ‖((w (cconj + g + topPl t) : ℝ) : ℂ) * GC Hs ψ (a / w (cconj + g + topPl t))
        - ((w' (cconj + g + topPl t) : ℝ) : ℂ) * GC Hs ψ (a / w' (cconj + g + topPl t))‖ ≤ K) :
    |balTop Hs a t w - balTop Hs a t w'| ≤ 2 * fPl H * K := by
  have e : balTop Hs a t w - balTop Hs a t w'
      = ((1 / ((PhiSet (H := H)).card : ℂ)) * ∑ g ∈ univ.filter (fun g : E0 × H => ¬ InPhi (g + topPl t)),
          ∑ ψ : AddChar (E0 × H) ℂ, ψ (-g) *
            (((w (cconj + g + topPl t) : ℝ) : ℂ) * GC Hs ψ (a / w (cconj + g + topPl t))
              - ((w' (cconj + g + topPl t) : ℝ) : ℂ) * GC Hs ψ (a / w' (cconj + g + topPl t)))).re := by
    unfold balTop
    rw [← Complex.sub_re, ← mul_sub, ← Finset.sum_sub_distrib]
    refine congrArg Complex.re (congrArg _ (Finset.sum_congr rfl fun g _ => ?_))
    rw [← Finset.sum_sub_distrib]
    exact Finset.sum_congr rfl fun ψ _ => by ring
  rw [e]
  refine le_trans (Complex.abs_re_le_norm _) ?_
  apply norm_avg_le _ (card_S_le t _ (Finset.Subset.refl _)) _ K hK0
  intro g hg ψ
  exact hK g (Finset.mem_filter.1 hg).2 ψ
end Formalism.LFunctionChainParameters.ThickSetMeanBounds.CR
