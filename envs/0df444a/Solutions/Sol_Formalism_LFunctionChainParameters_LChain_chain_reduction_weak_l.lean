-- Prove2me | solution 1 for Formalism.LFunctionChainParameters.LChain.chain_reduction_weak_l
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-25T17:17:48.220111+00:00
-- url     : https://prove2.me/submissions/ce23e987-fced-4809-9b99-578805911cbb

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
theorem _root_.solution : ChainCoreWeakL := by
  intro eD eL K cHH eK CL ε hε
  have hc : 0 < (|CL| + 1)⁻¹ := by positivity
  obtain ⟨x₀, hx₀⟩ := Filter.eventually_atTop.1
    (((isLittleO_log_rpow_atTop hε).bound hc).and (Filter.eventually_ge_atTop (2 : ℝ)))
  refine ⟨x₀, fun x hx h => ?_⟩
  obtain ⟨hb, hx2⟩ := hx₀ x hx
  have hlog : 0 < Real.log x := Real.log_pos (by linarith)
  rw [Real.norm_of_nonneg (Real.rpow_nonneg (by linarith) _), Real.norm_of_nonneg hlog.le] at hb
  have h1 : CL * Real.log x ≤ x ^ ε := by
    have h2 : (|CL| + 1) * Real.log x ≤ (|CL| + 1) * ((|CL| + 1)⁻¹ * x ^ ε) := by gcongr
    rw [mul_inv_cancel_left₀ (by positivity)] at h2
    have h3 : CL * Real.log x ≤ |CL| * Real.log x := by gcongr; exact le_abs_self CL
    linarith
  obtain ⟨H, i1, i2, i3, W, i4, i5, Top, i6, m, f, Dd, C, Xpp, D, ell, N, TT, T2, a, w, eT, eP, η, X', θ,
    hx', hε', heD, heL, hcHH, hHost, hId, hLed, hWin, hBN, ⟨r1, r2, r3⟩, hCost, hSize⟩ := h
  refine ⟨H, i1, i2, i3, W, i4, i5, Top, i6, m, f, Dd, C, Xpp, D, ell, N, TT, T2, a, w, eT, eP, η, X', θ,
    hx', hε', heD, heL, hcHH, hHost, hId, hLed, hWin, hBN, ⟨r1, r2, fun ψ hψ => ⟨(r3 ψ hψ).1, ?_⟩⟩, hCost, hSize⟩
  rw [div_mul_cancel₀ _ hlog.ne']
  exact (r3 ψ hψ).2.trans h1
end Formalism.LFunctionChainParameters.LChain
