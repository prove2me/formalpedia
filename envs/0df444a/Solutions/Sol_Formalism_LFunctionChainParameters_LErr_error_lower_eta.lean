-- Prove2me | solution 1 for Formalism.LFunctionChainParameters.LErr.error_lower_eta
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-24T10:44:17.412433+00:00
-- url     : https://prove2.me/submissions/d24be562-4a37-443e-ae6d-8c8b23874cff

import Definitions.Def_Formalism_SizeWindowBrackets_ErrorFormsWeakWindowsFalse
import Definitions.Def_Formalism_SizeWindowBrackets_ChainSlopeWindows_SubThreeMulLogTwoLe
import Theorems.Thm_Formalism_LFunctionChainParameters_LErr_core_lower

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
theorem _root_.solution : TraceTermLeErrorTerm := by
  intro U0 _ W _ _ Top _ m f D C Xpp eK K hW hdel0
  obtain ⟨hx, hε, hε1, hb, hxb, hnT, hm, hxm, heK, hk1, hkx, hka, hL0, hL, hLa0, hLa, hb', hkb', hX0,
    hXa, haT, hB0, hNc, hlW, hdel, heta, heB, hC⟩ := hW
  obtain ⟨c1, c1', c2, c2', c3, c3', c4, c4', c5, c5', c6, c6', c7, c7', hD, hLs, hHH⟩ := hC
  have hx0 : 0 < D.x := by linarith only [hx]
  have hb0 : 0 ≤ D.b := by linarith only [hb]
  have ha : 0 ≤ D.a := (mul_nonneg hx0.le hb0).trans hxb
  have hk : 0 < D.k := by linarith only [hk1]
  have hxH : 1 ≤ D.x ^ C.cHH := Real.one_le_rpow hx hHH
  have hdI : 1 ≤ (1 - D.delBar)⁻¹ :=
    (one_le_inv₀ (by linarith only [hdel])).2 (by linarith only [hdel0])
  have hlW0 : 0 ≤ umean (fun u0 => Real.log (Fintype.card (W u0) : ℝ)) :=
    div_nonneg (Finset.sum_nonneg (fun u0 _ => Real.log_natCast_nonneg _)) (Nat.cast_nonneg _)
  have het : 0 ≤ (D.etaBar + 4 * Real.sqrt D.eBar) * (D.x ^ C.cHH * D.b) := by positivity
  have := core_lower (nT := D.nT) (a := D.a) (b := D.b) (b' := D.b') (k := D.k) (L := D.L) (La := D.La)
    (B0 := D.B0) (Nc := D.Nc) (M := (m : ℝ)) (sA := D.sumA)
    (lW := umean (fun u0 => Real.log (Fintype.card (W u0) : ℝ))) (lk := Real.log D.k)
    (lH := Real.log (1 + D.x ^ C.cHH)) (dI := (1 - D.delBar)⁻¹)
    (et := (D.etaBar + 4 * Real.sqrt D.eBar) * (D.x ^ C.cHH * D.b)) (Xpp := Xpp)
    (yD := D.x ^ (C.eDiv * D.ε)) (yL := D.x ^ (C.eLoss * D.ε))
    (Real.rpow_nonneg hx0.le _) (Real.rpow_nonneg hx0.le _) (by linarith only [hnT]) ha hb0
    (Nat.cast_nonneg m) hk hL0 hLa0 hb' hX0 (Finset.sum_nonneg (fun t _ => (haT t).1)) hB0 hNc hlW0
    (Real.log_nonneg hk1) (Real.log_nonneg (by linarith only [hxH])) hdI het c1 c2 c3 c4 c5 c6 c7
  unfold errorTermWith UBar5 MLo5 Data.Vvar Data.LoP
  exact this
end Formalism.LFunctionChainParameters.LErr
