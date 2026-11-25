-- Prove2me | solution 1 for Formalism.LFunctionChainParameters.LChain.chain_at_alt
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-25T03:29:50.150305+00:00
-- url     : https://prove2.me/submissions/5fdcb663-6a0a-42e7-a970-b37fdf2fd754

import Definitions.Def_Formalism_SizeWindowBrackets_SChain
import Definitions.Def_Formalism_SizeWindowBrackets_ChainSlopeWindows_LevelOfCongruence
import Definitions.Def_Formalism_SizeWindowBrackets_ChainSlopeWindows_LipschitzWeightAndMinimum
import Definitions.Def_Formalism_SizeWindowBrackets_ChainSlopeWindows_SubThreeMulLogTwoLe
import Definitions.Def_Formalism_SizeWindowBrackets_ChainSlopeWindows_PChain
import Theorems.Thm_Formalism_LFunctionChainParameters_LChain_chain_top_bound
import Theorems.Thm_Formalism_LFunctionChainParameters_ThickSetMeanBounds_derivative_integral_all
import Theorems.Thm_Formalism_LFunctionChainParameters_ThickSetMeanBounds_lipschitz_weight_all
import Theorems.Thm_Formalism_LFunctionChainParameters_ThickSetMeanBounds_proposition_at_point


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Finset
noncomputable section
open Formalism Formalism.LFunctionChainParameters Formalism.LFunctionChainParameters.LChain
open Formalism Formalism.D5 Formalism.RankGapBounds.WeightedMeanData Formalism.LFunctionChainParameters.WeightedSlopeBounds Formalism.LFunctionChainParameters.characterSumData Formalism.LFunctionChainParameters.ThickSetMeanBounds Formalism.LFunctionChainParameters.LErr
namespace Formalism.LFunctionChainParameters.LChain
theorem _root_.solution : ChainAt := by
  obtain ⟨Cd, hCd, hDer⟩ := derivative_integral_all
  refine ⟨Cd, hCd, fun eD eL ε x h => ?_⟩
  obtain ⟨H, i1, i2, i3, D, ell, N, m, TT, T2, a, w, b, b', η, X', θ, CL, Err, k, aE, hD,
    ⟨h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11, h12, h13⟩, hS, hW⟩ := chain_top_bound Cd eD eL ε x h
  have := proposition_at_point (eD + eL + 3) ε x
    ⟨H, i1, i2, i3, D, ell, N, m, TT, T2, a, w, b, b', η, X', θ, Cd, CL, Err, k, aE, hD,
      ⟨h1, h2, h3, h4, h5, h6, h7, hCd, h8, h9, h10, h11, h12, lipschitz_weight_all H D ell, hDer H D ell, h13⟩, hS, hW⟩
  have e : eD + eL + 3 + 3 = eD + eL + 6 := by ring
  rwa [e] at this
end Formalism.LFunctionChainParameters.LChain
