-- Prove2me | solution 1 for Formalism.LFunctionChainParameters.LChain6.modulus_v_eventually
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-25T04:52:23.664907+00:00
-- url     : https://prove2.me/submissions/30909d60-61da-4e8b-ada0-44270eef71d7

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
import Theorems.Thm_Formalism_LFunctionChainParameters_CosetIndexLemmas_ev_exp
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
theorem _root_.solution : HostVEv := by
  intro ε A hε hA
  obtain ⟨y1, -, h1⟩ := CosetIndexLemmas.ev_exp 1 1 1 (ε / 30) one_pos (by positivity)
  obtain ⟨y2, h2⟩ := ((tendsto_rpow_atTop (show 0 < ε / 15 by positivity)).eventually_ge_atTop
    (A + 2)).exists_forall_of_atTop
  obtain ⟨y3, h3⟩ := ((tendsto_rpow_atTop (show 0 < ε / 5 by positivity)).eventually_ge_atTop 14).exists_forall_of_atTop
  refine ⟨max 3 (max y1 (max y2 y3)), fun x hx e q d he hq1 hq2 hd1 hd2 => ?_⟩
  have hx3 : 3 ≤ x := le_trans (le_max_left _ _) hx
  have hx' := le_trans (le_max_right _ _) hx
  have g1 := h1 x (le_trans (le_max_left _ _) hx')
  have hx'' := le_trans (le_max_right _ _) hx'
  have g2 := h2 x (le_trans (le_max_left _ _) hx'')
  have g3 := h3 x (le_trans (le_max_right _ _) hx'')
  have hx0 : 0 < x := by linarith
  have hx1 : 1 ≤ x := by linarith
  have hlx : Real.log x ≤ x ^ (ε / 30) := by
    rw [Real.log_le_iff_le_exp hx0]
    simpa using g1
  have hl1 : 1 ≤ Real.log x := by
    rw [Real.le_log_iff_exp_le hx0]
    have := Real.exp_one_lt_d9
    linarith
  have hX1 : X1 ε x ^ (1 / 2 : ℝ) = Real.exp (x ^ (ε / 5) * (1 / 2)) := by
    unfold X1; rw [← Real.exp_mul]
  have hX2 : X2 ε x ^ (1 / 2 : ℝ) = Real.exp (x ^ (ε / 5) * Real.log x ^ 2 * (1 / 2)) := by
    unfold X2; rw [← Real.exp_mul]
  have hy0 : 0 < x ^ (ε / 5) := Real.rpow_pos_of_pos hx0 _
  have hq8 : (8 : ℝ) ≤ (q : ℝ) := by
    have := Real.add_one_le_exp (x ^ (ε / 5) * (1 / 2))
    rw [hX1] at hq1
    linarith
  have hd8 : (8 : ℝ) ≤ (d : ℝ) := by
    have := Real.add_one_le_exp (x ^ (ε / 5) * Real.log x ^ 2 * (1 / 2))
    rw [hX2] at hd1
    have hl2 : 1 ≤ Real.log x ^ 2 := by nlinarith
    have : x ^ (ε / 5) ≤ x ^ (ε / 5) * Real.log x ^ 2 := by nlinarith
    linarith
  have hq0 : (0 : ℝ) < (q : ℝ) := by linarith
  have hd0 : (0 : ℝ) < (d : ℝ) := by linarith
  have hs8 : 8 ≤ Real.sqrt ((q : ℝ) * (d : ℝ)) := by
    rw [Real.le_sqrt' (by norm_num)]
    nlinarith
  have he0 : (0 : ℝ) ≤ (e : ℝ) := Nat.cast_nonneg _
  have hp1 : (2 : ℝ) ^ (-(e : ℝ)) ≤ 1 := Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by linarith)
  have hp0 : 0 < (2 : ℝ) ^ (-(e : ℝ)) := Real.rpow_pos_of_pos (by norm_num) _
  have hpw : (2 : ℝ) ^ (-1 : ℝ) ≤ (2 : ℝ) ^ ((e : ℝ) - (2 : ℝ) ^ (-(e : ℝ))) :=
    Real.rpow_le_rpow_of_exponent_le (by norm_num) (by linarith)
  have hhalf : (2 : ℝ) ^ (-1 : ℝ) = 1 / 2 := by
    rw [Real.rpow_neg (by norm_num), Real.rpow_one]; norm_num
  have hP0 : 0 < (2 : ℝ) ^ ((e : ℝ) - (2 : ℝ) ^ (-(e : ℝ))) := Real.rpow_pos_of_pos (by norm_num) _
  constructor
  · unfold hostV
    have := Real.pi_le_four
    rw [hhalf] at hpw
    nlinarith
  · have hS0 : 0 < Real.sqrt ((q : ℝ) * (d : ℝ)) := by linarith
    unfold hostV
    rw [Real.log_mul (by norm_num) (mul_pos hP0 hS0).ne', Real.log_mul hP0.ne' hS0.ne',
      Real.log_rpow (by norm_num), Real.log_sqrt (mul_pos hq0 hd0).le, Real.log_mul hq0.ne' hd0.ne']
    have hl2 : 0 ≤ Real.log 2 := Real.log_nonneg (by norm_num)
    have hl2' : Real.log 2 ≤ 1 := by
      have := Real.log_le_sub_one_of_pos (show (0 : ℝ) < 2 by norm_num)
      linarith
    have hee : (e : ℝ) * Real.log 2 ≤ A * Real.log x := by
      have h := Real.log_le_log (by positivity) he
      rw [Real.log_rpow hx0] at h
      push_cast at h
      rw [Real.log_pow] at h
      exact h
    have hlq : Real.log (q : ℝ) ≤ x ^ (ε / 5) := by
      have h := Real.log_le_log hq0 hq2
      unfold X1 at h
      rwa [Real.log_exp] at h
    have hld : Real.log (d : ℝ) ≤ x ^ (ε / 5) * Real.log x ^ 2 := by
      have h := Real.log_le_log hd0 hd2
      unfold X2 at h
      rwa [Real.log_exp] at h
    set z : ℝ := x ^ (4 * ε / 15) with hz
    have hz1 : 1 ≤ z := Real.one_le_rpow hx1 (by positivity)
    have c1 : x ^ (ε / 30) ≤ z := Real.rpow_le_rpow_of_exponent_le hx1 (by linarith)
    have c2 : x ^ (ε / 5) ≤ z := Real.rpow_le_rpow_of_exponent_le hx1 (by linarith)
    have c3 : x ^ (ε / 5) * Real.log x ^ 2 ≤ z := by
      have e1 : z = x ^ (ε / 5) * (x ^ (ε / 30)) ^ 2 := by
        rw [hz, sq, ← Real.rpow_add hx0, ← Real.rpow_add hx0]; congr 1; ring
      rw [e1]
      have : Real.log x ^ 2 ≤ (x ^ (ε / 30)) ^ 2 := pow_le_pow_left₀ (by linarith) hlx 2
      gcongr
    have c4 : x ^ (ε / 3) = x ^ (ε / 15) * z := by
      rw [hz, ← Real.rpow_add hx0]; congr 1; ring
    have c5 : ((e : ℝ) - (2 : ℝ) ^ (-(e : ℝ))) * Real.log 2 ≤ (e : ℝ) * Real.log 2 := by nlinarith
    have c6 : A * Real.log x ≤ A * z := by
      have : Real.log x ≤ z := le_trans hlx c1
      gcongr
    rw [c4]
    have c7 : (A + 2) * z ≤ x ^ (ε / 15) * z := by gcongr
    linarith
end Formalism.LFunctionChainParameters.LChain6
