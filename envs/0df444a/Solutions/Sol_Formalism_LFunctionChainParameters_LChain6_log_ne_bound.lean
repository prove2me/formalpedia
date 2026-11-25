-- Prove2me | solution 1 for Formalism.LFunctionChainParameters.LChain6.log_ne_bound
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-25T03:35:43.060795+00:00
-- url     : https://prove2.me/submissions/ecab2736-d795-450d-8369-6ac6b39104a3

import Definitions.Def_Formalism_SizeWindowBrackets_SlopesFromSizeAndCount
import Definitions.Def_Formalism_SizeWindowBrackets_ChainSlopeWindows_ChainLatticeSizesModelEventually
import Definitions.Def_Formalism_SizeWindowBrackets_ChainSlopeWindows_PrimeCongruenceConditions
import Definitions.Def_Formalism_SizeWindowBrackets_ChainSlopeWindows_PBrDiv
import Definitions.Def_Formalism_SizeWindowBrackets_ChainSlopeWindows_SecondPriceSumWeightsUncovered
import Definitions.Def_Formalism_SizeWindowBrackets_ChainSlopeWindows_ExistsOrthonormalFrameComplement
import Definitions.Def_Formalism_SizeWindowBrackets_ChainSlopeWindows_DisplayedInequalitySharpHalf
import Definitions.Def_Formalism_SizeWindowBrackets_ChainSlopeWindows_PSmall
import Definitions.Def_Formalism_SizeWindowBrackets_ChainSlopeWindows_LocalizationStructureHolds
import Definitions.Def_Formalism_LandauZeroFreeBounds_ExceptionalZeroBounds_ZetaNegReal
import Definitions.Def_Formalism_SizeWindowBrackets_ChainSlopeWindows_ChiEightNoRealZeroHypothesis
import Definitions.Def_Formalism_SizeWindowBrackets_ChainSlopeWindows_AnalyticFirstToLatticeDiscriminant
import Theorems.Thm_Formalism_LFunctionChainParameters_PrimeWindowSizeBounds_Facts_X1


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Module NumberField Matrix IsDedekindDomain
open Formalism.HN
noncomputable section
open Formalism Formalism.LFunctionChainParameters Formalism.LFunctionChainParameters.LChain6
open Formalism Formalism.D5 Formalism.RankGapBounds.WeightedMeanData Formalism.LFunctionChainParameters.WeightedSlopeBounds Formalism.LFunctionChainParameters.characterSumData Formalism.LFunctionChainParameters.ThickSetMeanBounds Formalism.LFunctionChainParameters.LErr Formalism.LFunctionChainParameters.LChain
  Formalism.LFunctionChainParameters.LChain2 Formalism.LFunctionChainParameters.LHost Formalism.LFunctionChainParameters.LBr2 Formalism.LFunctionChainParameters.LBrDiv Formalism.LFunctionChainParameters.SectionsFourToSixTransfer
namespace Formalism.LFunctionChainParameters.LChain6
theorem _root_.solution : LogNE := by
  intro ε A hε hA
  obtain ⟨y1, h1⟩ := ((tendsto_rpow_atTop (show 0 < ε / 5 by positivity)).eventually_ge_atTop
    (max A 3)).exists_forall_of_atTop
  refine ⟨max 8 y1, fun x hx n q d hn1 hn hq1 hq2 hd1 hd2 => ?_⟩
  have hx8 : 8 ≤ x := le_trans (le_max_left _ _) hx
  have g1 := h1 x (le_trans (le_max_right _ _) hx)
  have hyA : A ≤ x ^ (ε / 5) := le_trans (le_max_left _ _) g1
  have hy3 : 3 ≤ x ^ (ε / 5) := le_trans (le_max_right _ _) g1
  have hx0 : 0 < x := by linarith
  have hL2 : 2 ≤ Real.log x := by
    rw [Real.le_log_iff_exp_le hx0]
    have h := Real.exp_one_lt_d9
    have e2 : Real.exp 2 = Real.exp 1 * Real.exp 1 := by rw [← Real.exp_add]; norm_num
    have e0 := Real.exp_pos 1
    rw [e2]
    nlinarith
  have hX1 : X1 ε x ^ (1 / 2 : ℝ) = Real.exp (x ^ (ε / 5) * (1 / 2)) := by
    unfold X1; rw [← Real.exp_mul]
  have hX2 : X2 ε x ^ (1 / 2 : ℝ) = Real.exp (x ^ (ε / 5) * Real.log x ^ 2 * (1 / 2)) := by
    unfold X2; rw [← Real.exp_mul]
  have hq0 : (0 : ℝ) < (q : ℝ) := lt_trans (by rw [hX1]; exact Real.exp_pos _) hq1
  have hd0 : (0 : ℝ) < (d : ℝ) := lt_trans (by rw [hX2]; exact Real.exp_pos _) hd1
  have a1 : x ^ (ε / 5) / 2 < Real.log q := by
    have h := Real.log_lt_log (by rw [hX1]; exact Real.exp_pos _) hq1
    rw [hX1, Real.log_exp] at h
    linarith
  have a2 : Real.log q ≤ x ^ (ε / 5) := by
    have h := Real.log_le_log hq0 hq2
    unfold X1 at h
    rwa [Real.log_exp] at h
  have a3 : x ^ (ε / 5) * Real.log x ^ 2 / 2 < Real.log d := by
    have h := Real.log_lt_log (by rw [hX2]; exact Real.exp_pos _) hd1
    rw [hX2, Real.log_exp] at h
    linarith
  have a4 : Real.log d ≤ x ^ (ε / 5) * Real.log x ^ 2 := by
    have h := Real.log_le_log hd0 hd2
    unfold X2 at h
    rwa [Real.log_exp] at h
  refine ⟨a1, a2, a3, a4, ?_⟩
  have hn0 : (0 : ℝ) < (n : ℝ) := by exact_mod_cast hn1
  have hln : Real.log n ≤ A * Real.log x := by
    have h := Real.log_le_log hn0 hn
    rwa [Real.log_rpow hx0] at h
  have hl4 : Real.log 4 ≤ 3 := by
    have := Real.log_le_sub_one_of_pos (show (0 : ℝ) < 4 by norm_num)
    linarith
  push_cast
  rw [Real.log_mul (by positivity) hd0.ne', Real.log_mul (by positivity) hq0.ne',
    Real.log_mul (by norm_num) hn0.ne']
  set y : ℝ := x ^ (ε / 5) with hy
  set L : ℝ := Real.log x with hL
  have b1 : A * L ≤ y * L := by gcongr
  have b2 : 2 * y ≤ y * L := by nlinarith
  have b3 : 2 * (y * L) ≤ y * L ^ 2 := by nlinarith [mul_nonneg (by linarith : (0 : ℝ) ≤ y) (by linarith : (0 : ℝ) ≤ L)]
  linarith
end Formalism.LFunctionChainParameters.LChain6
