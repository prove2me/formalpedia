-- Prove2me | solution 1 for Formalism.LFunctionChainParameters.LChain6.ev_auxiliary
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-25T04:47:25.982806+00:00
-- url     : https://prove2.me/submissions/1c44df5f-2a75-46d2-999e-fc077b670bf4

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
import Theorems.Thm_Formalism_LFunctionChainParameters_LChain6_rpow_third_le
import Theorems.Thm_Formalism_LFunctionChainParameters_CosetIndexLemmas_ev_exp


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
theorem _root_.solution (ε A c' K cHH : ℝ) (hε : 0 < ε) (hε4 : ε < 1 / 4) (hc' : 0 < c') :
    ∃ x₀ : ℝ, ∀ x : ℝ, x₀ ≤ x → 20 ≤ x ∧ E8 x ε ≤ x ^ (-cHH) / 2 ∧ 6 ≤ x ^ ((1 : ℝ) / 2 - ε) ∧
      2 * K + 2 ≤ 15 * x ^ ((1 : ℝ) / 2 - ε) ∧ 4 * Real.exp (x ^ (ε / 4)) ≤ bpTx x ε ∧
      ∀ f : ℝ, 0 ≤ f → f ≤ 2 * x ^ A →
        2 * f * (x + 1) * Real.exp (-c' * x ^ (ε / 8)) ≤ 1 / x ∧
        6 * f * (x + 1) * (Real.exp (x ^ (ε / 4)) + 1) ≤ bTx x ε / x := by
  obtain ⟨y1, -, h1⟩ := CosetIndexLemmas.ev_exp 2 cHH 1 (ε / 8) one_pos (by positivity)
  obtain ⟨y2, h2⟩ := ((tendsto_rpow_atTop (show 0 < (1 : ℝ) / 2 - ε by linarith)).eventually_ge_atTop
    (max 6 ((2 * K + 2) / 15))).exists_forall_of_atTop
  obtain ⟨y3, h3⟩ := ((tendsto_rpow_atTop (show 0 < 2 * ε / 3 by positivity)).eventually_ge_atTop 2).exists_forall_of_atTop
  obtain ⟨y4, -, h4⟩ := CosetIndexLemmas.ev_exp 8 (A + 2) c' (ε / 8) hc' (by positivity)
  obtain ⟨y5, -, h5⟩ := CosetIndexLemmas.ev_exp 48 (A + 2) 1 (ε / 3) one_pos (by positivity)
  refine ⟨max 20 (max y1 (max y2 (max y3 (max y4 y5)))), fun x hx => ?_⟩
  have hx20 : 20 ≤ x := le_trans (le_max_left _ _) hx
  have hx' := le_trans (le_max_right _ _) hx
  have g1 := h1 x (le_trans (le_max_left _ _) hx')
  have hx'' := le_trans (le_max_right _ _) hx'
  have g2 := h2 x (le_trans (le_max_left _ _) hx'')
  have hx3 := le_trans (le_max_right _ _) hx''
  have g3 := h3 x (le_trans (le_max_left _ _) hx3)
  have hx4 := le_trans (le_max_right _ _) hx3
  have g4 := h4 x (le_trans (le_max_left _ _) hx4)
  have g5 := h5 x (le_trans (le_max_right _ _) hx4)
  have hx0 : 0 < x := by linarith
  have hx1 : 1 ≤ x := by linarith
  have hsum := rpow_third_le ε x hε hx1 g3
  have hA2 : x ^ (A + 2) = x ^ A * x * x := by
    rw [Real.rpow_add hx0, show (2 : ℝ) = 1 + 1 by norm_num, Real.rpow_add hx0, Real.rpow_one]; ring
  have hxA : 0 < x ^ A := Real.rpow_pos_of_pos hx0 _
  refine ⟨hx20, ?_, le_trans (le_max_left _ _) g2, ?_, ?_, fun f hf0 hf => ⟨?_, ?_⟩⟩
  · unfold E8
    rw [Real.exp_neg, Real.rpow_neg hx0.le]
    rw [one_mul] at g1
    have hp : 0 < x ^ cHH := Real.rpow_pos_of_pos hx0 _
    rw [inv_eq_one_div, inv_eq_one_div, div_div, div_le_div_iff₀ (Real.exp_pos _) (by positivity)]
    linarith
  · have := le_trans (le_max_right _ _) g2
    rw [div_le_iff₀ (by norm_num)] at this
    linarith
  · unfold bpTx aTx bTx XpTx
    rw [le_div_iff₀ (Real.exp_pos _)]
    have e1 : Real.exp (x ^ (ε / 4)) * Real.exp (x ^ (ε / 3)) ≤ Real.exp (x ^ ε) := by
      rw [← Real.exp_add]; exact Real.exp_le_exp.2 (by linarith)
    have e0 : 0 < Real.exp (x ^ ε) := Real.exp_pos _
    nlinarith
  · rw [neg_mul, Real.exp_neg, le_div_iff₀ hx0]
    have e0 : 0 < Real.exp (c' * x ^ (ε / 8)) := Real.exp_pos _
    rw [hA2] at g4
    have k1 : 2 * f * (x + 1) * x ≤ 8 * (x ^ A * x * x) := by
      have : 2 * f * (x + 1) * x ≤ 2 * (2 * x ^ A) * (x + 1) * x := by gcongr
      have k2 : 2 * (2 * x ^ A) * (x + 1) * x ≤ 2 * (2 * x ^ A) * (2 * x) * x := by gcongr; linarith
      nlinarith
    calc 2 * f * (x + 1) * (Real.exp (c' * x ^ (ε / 8)))⁻¹ * x
        = (2 * f * (x + 1) * x) * (Real.exp (c' * x ^ (ε / 8)))⁻¹ := by ring
      _ ≤ Real.exp (c' * x ^ (ε / 8)) * (Real.exp (c' * x ^ (ε / 8)))⁻¹ := by
          gcongr; exact le_trans k1 g4
      _ = 1 := mul_inv_cancel₀ e0.ne'
  · rw [le_div_iff₀ hx0]
    unfold bTx
    rw [hA2, one_mul] at g5
    have e4 : 1 ≤ Real.exp (x ^ (ε / 4)) := Real.one_le_exp (Real.rpow_nonneg hx0.le _)
    have e1 : Real.exp (x ^ (ε / 3)) * Real.exp (x ^ (ε / 4)) ≤ Real.exp (x ^ ε) := by
      rw [← Real.exp_add]; exact Real.exp_le_exp.2 hsum
    have k1 : 6 * f * (x + 1) * (Real.exp (x ^ (ε / 4)) + 1) * x
        ≤ 6 * (2 * x ^ A) * (2 * x) * (2 * Real.exp (x ^ (ε / 4))) * x := by
      gcongr <;> linarith
    calc 6 * f * (x + 1) * (Real.exp (x ^ (ε / 4)) + 1) * x
        ≤ 6 * (2 * x ^ A) * (2 * x) * (2 * Real.exp (x ^ (ε / 4))) * x := k1
      _ = (48 * (x ^ A * x * x)) * Real.exp (x ^ (ε / 4)) := by ring
      _ ≤ Real.exp (x ^ (ε / 3)) * Real.exp (x ^ (ε / 4)) := by gcongr
      _ ≤ Real.exp (x ^ ε) := e1
end Formalism.LFunctionChainParameters.LChain6
