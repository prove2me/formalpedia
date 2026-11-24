-- Prove2me | solution 1 for Formalism.LFunctionChainParameters.LBrDiv.construct_height_comparison
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-24T10:44:16.376721+00:00
-- url     : https://prove2.me/submissions/91905c28-0575-4030-b2d5-972c9fc23abd

import Definitions.Def_Formalism_SizeWindowBrackets_SBrDiv
import Definitions.Def_Formalism_SizeWindowBrackets_ChainSlopeWindows_LevelOfCongruence
import Definitions.Def_Formalism_SizeWindowBrackets_ChainSlopeWindows_StronglyIrreducible
import Definitions.Def_Formalism_HarderNarasimhan_HarderNarasimhanProofs_DualPl
import Definitions.Def_Formalism_HarderNarasimhan_HarderNarasimhanProofs_SizeMu
import Definitions.Def_Formalism_HarderNarasimhan_HarderNarasimhanProofs_Rerealize
import Definitions.Def_Formalism_SizeWindowBrackets_ChainSlopeWindows_PBrDiv
import Theorems.Thm_Formalism_LFunctionChainParameters_LBrDiv_height_comparison_of_constant
import Theorems.Thm_Formalism_LFunctionChainParameters_LBrDiv_univ_map_top
import Theorems.Thm_Formalism_LFunctionChainParameters_LBrDiv_threshold_constant_nonneg

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Module NumberField IsDedekindDomain
open Formalism.HN
noncomputable section
open Formalism Formalism.LFunctionChainParameters Formalism.LFunctionChainParameters.LBrDiv
open Formalism Formalism.D5 Formalism.RankGapBounds.WeightedMeanData Formalism.LFunctionChainParameters.WeightedSlopeBounds Formalism.LFunctionChainParameters.characterSumData Formalism.LFunctionChainParameters.LErr Formalism.LFunctionChainParameters.LChain2
namespace Formalism.LFunctionChainParameters.LBrDiv
theorem _root_.solution : HeightVariationOfCorrectedHeightBoundArith := by
  intro H _ _ _ W _ m G C D ell N TT T2 a w Fm C0 hC hx hLa h
  refine height_comparison_of_constant H W TT m _ (mkData G C.cHH D ell N TT T2 a w Fm) C C0 (E0 × H)
    ((Function.Embedding.subtype _).trans (topEmb H)) (fun ρ => a ρ.2) (fun t => rfl) hC
    (mul_nonneg hx (Real.exp_pos _).le) hLa (threshold_constant_nonneg (H := H) m G.x G.ε hx) ?_
  intro u0
  rw [univ_map_top]
  exact h u0
end Formalism.LFunctionChainParameters.LBrDiv
