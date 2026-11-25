-- Prove2me | solution 1 for Formalism.LFunctionChainParameters.LChain.chain_reduction_of_top
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-25T17:17:44.019432+00:00
-- url     : https://prove2.me/submissions/d90c302e-1f3c-4868-b0ab-d0471da8d2ec

import Definitions.Def_Formalism_SizeWindowBrackets_SChain
import Definitions.Def_Formalism_SizeWindowBrackets_ChainSlopeWindows_LevelOfCongruence
import Definitions.Def_Formalism_SizeWindowBrackets_ChainSlopeWindows_LipschitzWeightAndMinimum
import Definitions.Def_Formalism_SizeWindowBrackets_ChainSlopeWindows_SubThreeMulLogTwoLe
import Definitions.Def_Formalism_SizeWindowBrackets_ChainSlopeWindows_PChain
import Theorems.Thm_Formalism_LFunctionChainParameters_LChain_data_completion_bounds

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
theorem _root_.solution : ChainCoreOfTop := by
  intro H i1 i2 i3 Top i6 m f D0 C Xpp eK K CL D ell N TT T2 a w eT eP η X' θ hHost hId hWin hBN hRest hCost hSize
    hS0 hS1 hTop
  obtain ⟨⟨w1, w2, w3, w4, w5, w6, w7, w8, w9, w10, w11, w12, w13, w14, w15, w16, w17, w18, w19, w20, w21, w22,
    w23, w24, w25, w26, w27, wC⟩, wEta⟩ := hWin
  have wC' := wC
  obtain ⟨c1, c2, c3, c4, c5, c6, c7, c8, c9, c10, c11, c12, c13, c14, c15, c16, c17⟩ := wC'
  have hx0 : 0 < D0.x := by linarith
  have hb0 : 0 < D0.b := by linarith
  have ha0 : 0 ≤ D0.a := le_trans (by positivity) w5
  have hf : 0 < f := Fin.pos (eP.symm ⟨0, by simp [PhiSet, InPhi]⟩)
  have hw : ∀ u0 j ρ, 0 < D0.w u0 j ρ := by
    intro u0 j ρ
    rw [hId.2.1 u0 j ρ]
    exact hRest.1.2.2.2.2.2.2.1.1 u0 j _ (Finset.mem_filter.1 (eP ρ).2).2
  have hLed := data_completion_bounds D0 C Xpp hx0 hb0 ha0 w17 w10 w15 w22 w19 hf (fun t => (w21 t).1) hw
    ⟨c3, c5, c7, c9, c11, c13⟩ hS0 hS1 hTop
  have hnT : 0 ≤ D0.nT := by linarith
  refine ⟨H, i1, i2, i3, fun _ => Unit, inferInstance, inferInstance, Top, i6, m, f, compl D0 C, C, Xpp, D, ell, N,
    TT, T2, a, w, eT, eP, η, X', θ, rfl, rfl, le_refl _, le_refl _, le_refl _, hHost, hId, hLed, ?_, hBN, hRest, hCost,
    hSize⟩
  refine ⟨⟨w1, w2, w3, w4, w5, w6, w7, w8, w9, w10, w11, w12, w13, w14, w15, w16, w17, w18, w19, w20, w21, w22,
    w23, w24, ?_, le_refl _, le_refl _, wC⟩, ?_⟩
  · show (0 : ℝ) ≤ 1 / 2
    norm_num
  · have h1 : 0 ≤ K * D0.x ^ D0.ε * (D0.nT * D0.a) := by
      have hK : 0 ≤ K := le_trans c1 c2
      positivity
    show ((0 : ℝ) + 4 * Real.sqrt 0) * (D0.x ^ C.cHH * D0.b) ≤ K * D0.x ^ D0.ε * (D0.nT * D0.a)
    simpa using h1
end Formalism.LFunctionChainParameters.LChain
