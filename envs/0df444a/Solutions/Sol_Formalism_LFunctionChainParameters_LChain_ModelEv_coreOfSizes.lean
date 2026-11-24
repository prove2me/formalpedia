-- Prove2me | solution 1 for Formalism.LFunctionChainParameters.LChain.ModelEv.coreOfSizes
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-24T11:28:32.370444+00:00
-- url     : https://prove2.me/submissions/66b24ac9-d8ad-497c-867a-bda51235481a

import Definitions.Def_Formalism_SizeWindowBrackets_SChain
import Definitions.Def_Formalism_SizeWindowBrackets_ChainSlopeWindows_LevelOfCongruence
import Definitions.Def_Formalism_SizeWindowBrackets_ChainSlopeWindows_LipschitzWeightAndMinimum
import Definitions.Def_Formalism_SizeWindowBrackets_ChainSlopeWindows_SubThreeMulLogTwoLe
import Definitions.Def_Formalism_SizeWindowBrackets_ChainSlopeWindows_PChain
import Theorems.Thm_Formalism_LFunctionChainParameters_LChain_exists_data_completion

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
open Formalism.LFunctionChainParameters.LChain.ModelEv
open Model
namespace Formalism.LFunctionChainParameters.LChain.ModelEv
theorem _root_.solution {K cHH eK ε x : ℝ} (h : SizesAt K cHH eK ε x) : ChainCoreNoAnalytic 1 1 K cHH eK ε x := by
  obtain ⟨H, i1, i2, i3, Top, i6, m, f, D0, C, Xpp, D, ell, N, TT, T2, a, w, eT, eP, η, X', θ, hx, hε, heD, heL, hcHH,
    hHost, hId, hWin, hBN, hSz, hθ, hCost, hSize, hS0, hS1, hTop⟩ := h
  subst hx hε
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
    exact hSz.2.2.2.2.2.2.1.1 u0 j _ (Finset.mem_filter.1 (eP ρ).2).2
  obtain ⟨D1, ⟨s1, s2, s3, s4, s5, s6, s7, s8, s9, s10, s11, s12, s13, s14, s15⟩, z1, z2, z3, hLed⟩ :=
    exists_data_completion D0 C Xpp hx0 hb0 ha0 w17 w10 w15 w22 w19 hf (fun t => (w21 t).1) hw
      ⟨c3, c5, c7, c9, c11, c13⟩ hS0 hS1 hTop
  have hnT : D1.nT = D0.nT := rfl
  refine ⟨H, i1, i2, i3, fun _ => Unit, inferInstance, inferInstance, Top, i6, m, f, D1, C, Xpp, D, ell, N,
    TT, T2, a, w, eT, eP, η, X', θ, s1, s2, heD, heL, hcHH, hHost, ?_, hLed, ?_, ?_, ?_, hθ, ?_, ?_⟩
  · obtain ⟨j1, j2, j3, j4, j5⟩ := hId
    exact ⟨by rw [s13]; exact j1, by rw [s14]; exact j2, by rw [s11]; exact j3, by rw [s12]; exact j4,
      by rw [s15]; exact j5⟩
  · refine ⟨?_, ?_⟩
    · unfold ErrWindows0
      rw [s1, s2, s3, s4, s5, s6, s7, s8, s9, s10, s13, z1, z2, z3, hnT]
      exact ⟨w1, w2, w3, w4, w5, w6, w7, w8, w9, w10, w11, w12, w13, w14, w15, w16, w17, w18, w19, w20, w21, w22,
        w23, w24, by norm_num, le_refl _, le_refl _, wC⟩
    · rw [s1, s2, s3, s4, z2, z3, hnT]
      have h1 : 0 ≤ K * D0.x ^ D0.ε * (D0.nT * D0.a) := by
        have hK : 0 ≤ K := le_trans c1 c2
        have : 0 ≤ D0.nT := by linarith
        positivity
      simpa using h1
  · unfold BNBounds
    rw [s1, s2, s4, s6, s9, s10]
    exact hBN
  · rw [s4, s5]; exact hSz
  · rw [s4]; exact hCost
  · rw [s3, s4, s6]; exact hSize
end Formalism.LFunctionChainParameters.LChain.ModelEv
