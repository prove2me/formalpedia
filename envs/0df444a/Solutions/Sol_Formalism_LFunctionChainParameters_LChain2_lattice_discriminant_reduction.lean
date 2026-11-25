-- Prove2me | solution 1 for Formalism.LFunctionChainParameters.LChain2.lattice_discriminant_reduction
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-25T03:27:05.743438+00:00
-- url     : https://prove2.me/submissions/65e65613-ada4-41e3-9bee-c0af2e521a25

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
import Theorems.Thm_Formalism_LFunctionChainParameters_LChain2_hostV_pos
import Theorems.Thm_Formalism_LFunctionChainParameters_LChain2_inputs_discriminant_iff

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
theorem _root_.solution : Core2dToCore2c := by
  rintro Cord eD eL K cHH eK CL eW KW ε x ⟨e, q, d, i1, i2, Ω, i3, W, i4, i5, m, G, C, cT, N, TT, T2, a, w, Fm, Lp, P,
    π, s, sB, BAD, Sig, η, θ, g₁, g₂, logOm, hHyp, hx, hε, heD, heL, hcHH, hPe, hv, -, -, -, hPer, hL, hB⟩
  refine ⟨e, q, d, i1, i2, Ω, i3, W, i4, i5, m, G, C, cT, N, TT, T2, a, w, Fm, Lp, P, π, s, sB, BAD, Sig, η, θ,
    hHyp, hx, hε, heD, heL, hcHH, hPe, hL, fun o ho => ?_⟩
  refine (inputs_discriminant_iff _ _ G C cT N TT T2 (a o) (w o) (Fm o) η θ eK K CL).2 ⟨?_, ?_⟩
  · rw [hv]
    exact hostV_pos e q d hHyp.1 hHyp.2.1
  · have h := hB o ho
    unfold PerHost at hPer
    rw [hv, ← hPer]
    exact h
end Formalism.LFunctionChainParameters.LChain2
