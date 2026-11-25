-- Prove2me | solution 1 for Formalism.LFunctionChainParameters.LChain2.lattice_complete_reduction
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-25T04:16:54.501245+00:00
-- url     : https://prove2.me/submissions/68d84508-75cb-4e65-980b-9d31d2d03b45

import Definitions.Def_Formalism_SizeWindowBrackets_Chain2aCoreNoAnalytic
import Definitions.Def_Formalism_SizeWindowBrackets_ChainSlopeWindows_PChain
import Definitions.Def_Formalism_SizeWindowBrackets_ChainSlopeWindows_SlopeInequalityOfLattices
import Definitions.Def_Formalism_SizeWindowBrackets_ChainSlopeWindows_GaloisMapComplexConjugation
import Definitions.Def_Formalism_SizeWindowBrackets_ChainSlopeWindows_AdmissibleSchurLemma
import Definitions.Def_Formalism_SizeWindowBrackets_ChainSlopeWindows_OneLeThresholdMulPowers
import Definitions.Def_Formalism_SizeWindowBrackets_ChainSlopeWindows_StronglyIrreducible
import Definitions.Def_Formalism_SizeWindowBrackets_ChainSlopeWindows_ProjectiveLines
import Definitions.Def_Formalism_HarderNarasimhan_HarderNarasimhanProofs_SlopeIneqMean
import Definitions.Def_Formalism_HarderNarasimhan_HarderNarasimhanProofs_HtGram
import Definitions.Def_Formalism_HarderNarasimhan_HarderNarasimhanProofs_PolygonSlopeSum
import Definitions.Def_Formalism_HarderNarasimhan_HarderNarasimhanProofs_SizeMu
import Definitions.Def_Formalism_SizeWindowBrackets_ChainSlopeWindows_ChainLatticeSizesModelEventually
import Theorems.Thm_Formalism_LFunctionChainParameters_LChain2_losses_of_window
import Theorems.Thm_Formalism_LFunctionChainParameters_LHost_extension_facts
import Theorems.Thm_Formalism_LFunctionChainParameters_PrimeWindowSizeBounds_joint_bound_eventually


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Module NumberField Matrix
open Formalism.HN
noncomputable section
open Formalism Formalism.LFunctionChainParameters Formalism.LFunctionChainParameters.LChain2
open Formalism Formalism.D5 Formalism.RankGapBounds.WeightedMeanData Formalism.LFunctionChainParameters.WeightedSlopeBounds Formalism.LFunctionChainParameters.characterSumData Formalism.LFunctionChainParameters.ThickSetMeanBounds Formalism.LFunctionChainParameters.LErr Formalism.LFunctionChainParameters.LChain
namespace Formalism.LFunctionChainParameters.LChain2
theorem _root_.solution : Core2cToCore2 := by
  obtain ⟨Cord, h0, h⟩ := PrimeWindowSizeBounds.joint_bound_eventually
  refine ⟨Cord, h0, fun ε eW KW hε hε4 => ?_⟩
  obtain ⟨x₁, hx₁⟩ := h ε eW KW hε hε4
  refine ⟨x₁, ?_⟩
  rintro eD eL K cHH eK CL x hxx ⟨e, q, d, i1, i2, Ω, i3, W, i4, i5, m, G, C, cT, N, TT, T2, a, w, Fm, Lp, P, π,
    s, sB, BAD, Sig, η, θ, hHyp, hx, hεG, heD, heL, hcHH, -, hL, hB⟩
  have hL' := hL
  obtain ⟨px, pε, -, -, pC, hWin, hSet, -⟩ := hL'
  obtain ⟨o, hπ, hC⟩ := hx₁ P (pε.trans hεG) pC (by rw [px, hx]; exact hxx) hWin _ _ _ _ Ω π _ s sB _ TT BAD Sig _ _
    hSet
  have hBo := hB o hπ
  have hx1 : 1 ≤ G.x := hBo.2.2.2.2.2.2.2.2.2.2.2.2.2.1.1.1
  exact ⟨e, q, d, i1, i2, W o, i4 o, i5 o, m, G, C, cT, N, TT, T2, a o, w o, Fm o, η, θ, hHyp, hx, hεG, heD, heL,
    hcHH, hBo, losses_of_window _ (LHost.extension_facts e q d hHyp) _ G C N TT T2 a w Fm Lp P π s sB BAD
      Sig Cord eW KW o hL hx1 hC⟩
end Formalism.LFunctionChainParameters.LChain2
