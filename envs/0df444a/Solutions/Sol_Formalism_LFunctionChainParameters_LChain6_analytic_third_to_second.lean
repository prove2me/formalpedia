-- Prove2me | solution 1 for Formalism.LFunctionChainParameters.LChain6.analytic_third_to_second
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-25T04:46:18.090826+00:00
-- url     : https://prove2.me/submissions/4fed8a9c-e0e5-43d3-b534-2f5296be9b51

import Definitions.Def_Formalism_SizeWindowBrackets_SlopesFromSizeAndCount
import Definitions.Def_Formalism_SizeWindowBrackets_ChainSlopeWindows_ChainLatticeSizesModelEventually
import Definitions.Def_Formalism_SizeWindowBrackets_ChainSlopeWindows_PrimeCongruenceConditions
import Definitions.Def_Formalism_SizeWindowBrackets_ChainSlopeWindows_PBrDiv
import Definitions.Def_Formalism_SizeWindowBrackets_ChainSlopeWindows_SecondPriceSumWeightsUncovered
import Definitions.Def_Formalism_SizeWindowBrackets_ChainSlopeWindows_ExistsOrthonormalFrameComplement
import Definitions.Def_Formalism_SizeWindowBrackets_ChainSlopeWindows_DisplayedInequalitySharpHalf
import Definitions.Def_Formalism_SizeWindowBrackets_ChainSlopeWindows_PSmall
import Definitions.Def_Formalism_SizeWindowBrackets_ChainSlopeWindows_LocalizationStructureHolds
import Definitions.Def_Formalism_LandauZeroFreeBounds_ExceptionalZeroBounds_ZetaNegReal
import Definitions.Def_Formalism_SizeWindowBrackets_ChainSlopeWindows_ChiEightNoRealZeroHypothesis
import Definitions.Def_Formalism_SizeWindowBrackets_ChainSlopeWindows_AnalyticFirstToLatticeDiscriminant
import Theorems.Thm_Formalism_LFunctionChainParameters_LChain6_inputs_third_to_second

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Module NumberField Matrix IsDedekindDomain
open Formalism.HN
noncomputable section
open Formalism Formalism.LFunctionChainParameters Formalism.LFunctionChainParameters.LChain6
open Formalism Formalism.D5 Formalism.RankGapBounds.WeightedMeanData Formalism.LFunctionChainParameters.WeightedSlopeBounds Formalism.LFunctionChainParameters.characterSumData Formalism.LFunctionChainParameters.ThickSetMeanBounds Formalism.LFunctionChainParameters.LErr Formalism.LFunctionChainParameters.LChain
  Formalism.LFunctionChainParameters.LChain2 Formalism.LFunctionChainParameters.LHost Formalism.LFunctionChainParameters.LBr2 Formalism.LFunctionChainParameters.LBrDiv Formalism.LFunctionChainParameters.SectionsFourToSixTransfer
namespace Formalism.LFunctionChainParameters.LChain6
theorem _root_.solution : Core6cToCore6b := by
  rintro A c' Cord eD eL K cHH eK CL eW KW ε x ⟨e, q, d, i1, i2, Ω, i3, W, i4, i5, m, G, C, N, TT, T2, a, w, Fc, Rw, O, Lp,
    P, π, s, sB, BAD, Sig, η, g₁, g₂, logOm, C0, cZ, cL, cE5, c5, C0S, hx, hεG, heD, heL, hcHH, hPe, he, h25, hv, hg1, hg2,
    hlg, hPer, hL, hB⟩
  exact ⟨e, q, d, i1, i2, Ω, i3, W, i4, i5, m, G, C, N, TT, T2, a, w, fun o u0 => (Fc o u0).toFam, Rw, O, Lp, P, π, s, sB,
    BAD, Sig, η, g₁, g₂, logOm, C0, cZ, cL, cE5, c5, hx, hεG, heD, heL, hcHH, hPe, he, h25, hv, hg1, hg2, hlg, hPer, hL,
    fun o ho => inputs_third_to_second _ _ G C N TT T2 (a o) (w o) (Fc o) (Rw o) (O o) η _ eK K logOm C0 cZ cL cE5 c5 C0S g₁ g₂
      (hB o ho)⟩
end Formalism.LFunctionChainParameters.LChain6
