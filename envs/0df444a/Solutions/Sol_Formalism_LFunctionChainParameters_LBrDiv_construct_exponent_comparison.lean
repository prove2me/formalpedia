-- Prove2me | solution 1 for Formalism.LFunctionChainParameters.LBrDiv.construct_exponent_comparison
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-24T11:37:23.085537+00:00
-- url     : https://prove2.me/submissions/569d2bc2-07cf-4b3d-8c93-87994c348586

import Definitions.Def_Formalism_SizeWindowBrackets_SBrDiv
import Definitions.Def_Formalism_SizeWindowBrackets_ChainSlopeWindows_LevelOfCongruence
import Definitions.Def_Formalism_SizeWindowBrackets_ChainSlopeWindows_StronglyIrreducible
import Definitions.Def_Formalism_HarderNarasimhan_HarderNarasimhanProofs_DualPl
import Definitions.Def_Formalism_HarderNarasimhan_HarderNarasimhanProofs_SizeMu
import Definitions.Def_Formalism_HarderNarasimhan_HarderNarasimhanProofs_Rerealize
import Definitions.Def_Formalism_SizeWindowBrackets_ChainSlopeWindows_PBrDiv
import Theorems.Thm_Formalism_LFunctionChainParameters_LBrDiv_exponent_comparison_of_constant
import Theorems.Thm_Formalism_LFunctionChainParameters_LBrDiv_exponent_of_places
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
theorem _root_.solution : TypePrimeCostOfDeviationBoundArith := by
  intro H _ _ _ W _ m G C D ell N TT T2 a w Fm C0 g hg hC hx h
  refine exponent_comparison_of_constant H W TT m _ (mkData G C.cHH D ell N TT T2 a w Fm) C C0 (E0 × H)
    ((Function.Embedding.subtype _).trans (topEmb H)) (fun ρ => a ρ.2)
    (fun u0 u j => ∑ᶠ z : HeightOneSpectrum (𝓞 (Fm u0).K),
        lw z * (if plOf z ∈ (Fm u0).S then ramE (plOf z) * (Fm u0).Ej u j (plOf z) else 0))
    (fun t => rfl) (fun u0 u j => exponent_of_places (W u0) m (Fm u0) u j) hC
    (threshold_constant_nonneg (H := H) m G.x G.ε hx) ?_
  intro u0 u
  rw [univ_map_top]
  have h1 := h u0 u
  rw [← hg] at h1
  exact h1
end Formalism.LFunctionChainParameters.LBrDiv
