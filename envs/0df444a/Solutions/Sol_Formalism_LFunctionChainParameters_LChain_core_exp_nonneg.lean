-- Prove2me | solution 1 for Formalism.LFunctionChainParameters.LChain.core_exp_nonneg
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T04:35:00.762824+00:00
-- url     : https://prove2.me/submissions/b0473eda-15e7-480c-9dd5-f8da989440b0

import Definitions.Def_Formalism_SizeWindowBrackets_SChain
import Definitions.Def_Formalism_SizeWindowBrackets_ChainSlopeWindows_LevelOfCongruence
import Definitions.Def_Formalism_SizeWindowBrackets_ChainSlopeWindows_LipschitzWeightAndMinimum
import Definitions.Def_Formalism_SizeWindowBrackets_ChainSlopeWindows_SubThreeMulLogTwoLe
import Definitions.Def_Formalism_SizeWindowBrackets_ChainSlopeWindows_PChain

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
open Formalism Formalism.D5 Formalism.RankGapBounds.WeightedMeanData Formalism.LFunctionChainParameters.WeightedSlopeBounds Formalism.LFunctionChainParameters.characterSumData Formalism.LFunctionChainParameters.ThickSetMeanBounds Formalism.LFunctionChainParameters.ConditionalMainTheorem Formalism.LFunctionChainParameters.LErr
namespace Formalism.LFunctionChainParameters.LChain
theorem _root_.solution {eD eL K cHH eK CL ε x : ℝ} (h : ChainCore eD eL K cHH eK CL ε x) : 0 ≤ eD ∧ 0 ≤ eL ∧ 0 < ε := by
  obtain ⟨H, i1, i2, i3, W, i4, i5, Top, i6, m, f, Dd, C, Xpp, D, ell, N, TT, T2, a, w, eT, eP, η, X', θ,
    hx, hε, heD, heL, hcHH, hHost, hId, hLed, hWin, hBN, hRest, hCost, hSize⟩ := h
  obtain ⟨⟨w1, w2, w3, w4, w5, w6, w7, w8, w9, w10, w11, w12, w13, w14, w15, w16, w17, w18, w19, w20, w21, w22,
    w23, w24, w25, w26, w27, wC⟩, wEta⟩ := hWin
  obtain ⟨c1, c2, c3, c4, c5, c6, c7, c8, c9, c10, c11, c12, c13, c14, c15, c16, c17⟩ := wC
  exact ⟨by linarith, by linarith, hε ▸ w2⟩
end Formalism.LFunctionChainParameters.LChain
