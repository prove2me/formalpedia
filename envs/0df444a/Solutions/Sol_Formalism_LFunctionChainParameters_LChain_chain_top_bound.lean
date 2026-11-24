-- Prove2me | solution 1 for Formalism.LFunctionChainParameters.LChain.chain_top_bound
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-24T13:37:15.620712+00:00
-- url     : https://prove2.me/submissions/cd56848e-f4df-48d4-8941-fc1ae8815ab1

import Definitions.Def_Formalism_SizeWindowBrackets_SChain
import Definitions.Def_Formalism_SizeWindowBrackets_ChainSlopeWindows_LevelOfCongruence
import Definitions.Def_Formalism_SizeWindowBrackets_ChainSlopeWindows_LipschitzWeightAndMinimum
import Definitions.Def_Formalism_SizeWindowBrackets_ChainSlopeWindows_SubThreeMulLogTwoLe
import Definitions.Def_Formalism_SizeWindowBrackets_ChainSlopeWindows_PChain
import Theorems.Thm_Formalism_LFunctionChainParameters_LChain_small_costs_split
import Theorems.Thm_Formalism_LFunctionChainParameters_LChain_size_windows_split
import Theorems.Thm_Formalism_LFunctionChainParameters_LErr_joint_error_bound
import Theorems.Thm_Formalism_LFunctionChainParameters_ThickSetMeanBounds_top_from_weighted_mean
import Theorems.Thm_Formalism_LFunctionChainParameters_WeightedSlopeBounds_uniform_bound_statement


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
theorem _root_.solution : ChainTop := by
  rintro Cd eD eL ε x ⟨K, cHH, eK, CL, hCore, hx3, h26, hLX, hMove⟩
  obtain ⟨H, i1, i2, i3, W, i4, i5, Top, i6, m, f, Dd, C, Xpp, D, ell, N, TT, T2, a, w, eT, eP, η, X', θ,
    hx, hε, heD, heL, hcHH, hHost, hId, hLed, hWin, hBN, hRest, hCost, hSize⟩ := hCore
  subst hx hε
  obtain ⟨j1, j2, j3, j4, j5⟩ := hId
  obtain ⟨l1, l2, l3, l4, l5, l6, l7, l8, l9, l10, l11⟩ := hLed
  have hWin' := hWin
  obtain ⟨⟨w1, w2, w3, w4, w5, w6, w7, w8, w9, w10, w11, w12, w13, w14, w15, w16, w17, w18, w19, w20, w21, w22,
    w23, w24, w25, w26, w27, wC⟩, wEta⟩ := hWin'
  obtain ⟨c1, c2, c3, c4, c5, c6, c7, c8, c9, c10, c11, c12, c13, c14, c15, c16, c17⟩ := wC

  have hLX' : LargeX Dd.x Dd.ε K C.cHH eK := by
    refine ⟨hLX.1, le_trans ?_ hLX.2⟩
    unfold KBig
    exact mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left (by linarith) (by positivity)) (by linarith)

  have hTop : topExcess D N ell TT a w ≤
      Dd.x ^ (CErr C * Dd.ε) * errorBracketSizeWindows Dd.x Dd.ε (Fintype.card H) TT.card T2.card m Dd.b Dd.k Dd.a :=
    joint_error_bound (H := H) top_from_weighted_mean Dd C Xpp eK K D N ell TT T2 a w eT eP
      (uniform_bound_statement Dd C Xpp) l1 l2 l3 l4 l5 l6 l7 l8 l9 l10 l11 hWin hLX' hBN.1 hBN.2 j1 j2 j3 j4 j5
  have hb : 0 < Dd.b := by linarith
  have hx0 : 0 < Dd.x := by linarith
  have hk : 0 < Dd.k := by linarith
  have ha : 0 ≤ Dd.a := l1.2.2.1
  have hBr : 0 ≤ errorBracketSizeWindows Dd.x Dd.ε (Fintype.card H) TT.card T2.card m Dd.b Dd.k Dd.a := by
    unfold errorBracketSizeWindows
    positivity
  have hExp : Dd.x ^ (CErr C * Dd.ε) ≤ Dd.x ^ ((eD + eL + 3) * Dd.ε) := by
    refine Real.rpow_le_rpow_of_exponent_le w1 (mul_le_mul_of_nonneg_right ?_ w2.le)
    unfold CErr
    linarith
  have hTop' := le_trans hTop (mul_le_mul_of_nonneg_right hExp hBr)
  obtain ⟨⟨r1, r2, r3, r4, r5, r6, r7, r8⟩, r9, r10⟩ := hRest
  refine ⟨H, i1, i2, i3, D, ell, N, m, TT, T2, a, w, Dd.b, Dd.b', η, X', θ, CL,
    Dd.x ^ ((eD + eL + 3) * Dd.ε)
      * errorBracketSizeWindows Dd.x Dd.ε (Fintype.card H) TT.card T2.card m Dd.b Dd.k Dd.a,
    Dd.k, Dd.a, hHost, ⟨hx3, hb, r1, r2, r3, r4, r5, r6, r7, r8, hTop', r9, r10⟩,
    (small_costs_split _ _ _ _ _ _ _ _).2 ⟨hMove, hCost⟩, ?_⟩
  refine (size_windows_split _ _ _ _ _ _ _ _ _ _ _).2 ⟨hSize, le_refl _, ⟨hx3, h26⟩, w2, by linarith,
    Fintype.card_pos, hb, ha, Finset.card_le_univ T2, w7, w8⟩
end Formalism.LFunctionChainParameters.LChain
