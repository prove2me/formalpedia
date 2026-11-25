-- Prove2me | solution 1 for Formalism.LFunctionChainParameters.LErr.error_bound
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-25T17:17:20.062099+00:00
-- url     : https://prove2.me/submissions/81d8ab1c-02bf-4f87-be0e-949479167fb2

import Definitions.Def_Formalism_SizeWindowBrackets_ErrorFormsWeakWindowsFalse
import Definitions.Def_Formalism_SizeWindowBrackets_ChainSlopeWindows_SubThreeMulLogTwoLe
import Theorems.Thm_Formalism_LFunctionChainParameters_LErr_error_sizes_eventually
import Theorems.Thm_Formalism_LFunctionChainParameters_LErr_text_sizes_windows

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Real
open Formalism Formalism.LFunctionChainParameters Formalism.LFunctionChainParameters.LErr
open Formalism.RankGapBounds.WeightedMeanData Formalism.LFunctionChainParameters.WeightedSlopeBounds
set_option linter.unusedVariables false
namespace Formalism.LFunctionChainParameters.LErr
theorem _root_.solution : ErrorFormsEventualUnderSizeParameters := by
  intro ε K cHH eK hε
  obtain ⟨x1, hx1⟩ := error_sizes_eventually ε K cHH eK hε
  obtain ⟨x2, hx2⟩ := text_sizes_windows ε eK hε
  refine ⟨max x1 x2, ?_⟩
  intro U0 _ W _ _ Top _ m f D C Xpp n lrd h1 h2 hx hT
  obtain ⟨tb, ta, tb', tX, tL, tLa, tl0, tl, tn0, tn, tε, tnT, tm, txm, teK, tk1, tkx, taT, tB0, tNc, tW,
    td, te, teB, tet, tC⟩ := hT
  have hk0 : 0 < D.k := by linarith only [tk1]
  rw [h1] at tl
  obtain ⟨w1, w2, w3, w4, w5, w6, w7, w8, w9⟩ :=
    hx2 D.x D.k n lrd ((le_max_right _ _).trans hx) hk0 tkx tn0 tn tl
  rw [← h1] at w2 w3 w4 w5 w6 w7 w8 w9
  rw [← tb] at w2 w3
  rw [← ta] at w4 w5 w7 w9
  rw [← tb'] at w6 w7
  rw [← tX] at w8 w9
  have hxb : D.x * D.b ≤ D.a := by rw [ta, tb]; exact le_refl _
  have hy0 : 0 ≤ D.x ^ D.ε := Real.rpow_nonneg (by linarith only [w1]) _
  have ha1 : 1 ≤ D.a := by
    refine le_trans ?_ hxb
    exact one_le_mul_of_one_le_of_one_le w1 w2
  refine hx1 D C Xpp h1 h2 ((le_max_left _ _).trans hx) ⟨⟨w1, by rw [h1]; exact hε, tε, w2, hxb, tnT, tm,
    txm, teK, tk1, tkx, w5, ?_, ?_, ?_, ?_, w6, w7, w8, w9, taT, tB0, tNc, tW, td, te, teB, tC⟩, tet⟩
  · rw [tL, w3]; exact hy0
  · rw [tL, w3]; linarith only [hy0]
  · rw [tLa]; exact add_nonneg (Real.log_nonneg ha1) tl0
  · rw [tLa]; exact w4
end Formalism.LFunctionChainParameters.LErr
