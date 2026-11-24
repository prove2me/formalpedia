-- Prove2me | solution 1 for Formalism.LFunctionChainParameters.SectionsFourToSixTransfer.level_sizes
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-24T10:30:39.280221+00:00
-- url     : https://prove2.me/submissions/5b43359f-e8be-432f-9f5e-e9da514c55ee

import Definitions.Def_Formalism_SizeWindowBrackets_TranslateWordBoundHypotheses
import Definitions.Def_Formalism_SizeWindowBrackets_ChainSlopeWindows_LevelOfCongruence
import Definitions.Def_Formalism_SizeWindowBrackets_ChainSlopeWindows_SubThreeMulLogTwoLe
import Definitions.Def_Formalism_LogVandermondeBounds_HookGammaAmgmMultinomialBounds
import Definitions.Def_Formalism_SizeWindowBrackets_ChainSlopeWindows_SecondPriceSumWeightsUncovered

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Real
open Formalism Formalism.LFunctionChainParameters Formalism.LFunctionChainParameters.SectionsFourToSixTransfer
open Formalism.RankGapBounds.WeightedMeanData Formalism.LFunctionChainParameters.WeightedSlopeBounds Formalism.LFunctionChainParameters.LErr Formalism.LFunctionChainParameters.LatticeToWeightTransfer
namespace Formalism.LFunctionChainParameters.SectionsFourToSixTransfer
theorem _root_.solution : LevelSizes := by
  intro f m b T N hf hm hb hT hN hN2
  have hf1 : (1 : ℝ) ≤ (f : ℝ) := by exact_mod_cast hf
  have hb1 : 1 ≤ b := by linarith
  have hb0 : 0 < b := by linarith
  have hm3 : (3 : ℝ) ≤ (m : ℝ) / 2 := by
    have : (6 : ℝ) ≤ (m : ℝ) := by exact_mod_cast hm
    linarith
  have hb3 : b ^ 3 ≤ T := by
    have h := Real.rpow_le_rpow_of_exponent_le hb1 hm3
    have e : b ^ (3 : ℝ) = b ^ 3 := by
      rw [show (3 : ℝ) = ((3 : ℕ) : ℝ) by norm_num, Real.rpow_natCast]
    rw [e] at h
    linarith
  have h4f : 4 * (f : ℝ) ≤ T := by nlinarith
  have hT2 : 2 < T := by linarith
  have hT0 : 0 < T := by linarith
  have hA : 4 * (f : ℝ) / T * b ^ 2 ≤ 1 / 2 := by
    have e : 4 * (f : ℝ) / T * b ^ 2 = 4 * (f : ℝ) * b ^ 2 / T := by ring
    rw [e, div_le_iff₀ hT0]
    have : 8 * (f : ℝ) * b ^ 2 ≤ b * b ^ 2 := mul_le_mul_of_nonneg_right hb (sq_nonneg _)
    nlinarith
  have hB : (f : ℝ) * Real.log (T - 1) / (T - 2) ≤ 1 / 2 := by
    have hy : 0 < T - 1 := by linarith
    set s := Real.sqrt (T - 1) with hs
    have hs2 : s ^ 2 = T - 1 := Real.sq_sqrt hy.le
    have h8 : (8 * (f : ℝ)) ^ 3 ≤ b ^ 3 := pow_le_pow_left₀ (by positivity) hb 3
    have hs8 : 8 * (f : ℝ) ≤ s := by
      apply Real.le_sqrt_of_sq_le
      nlinarith [mul_nonneg (sq_nonneg (f : ℝ)) (by linarith : (0 : ℝ) ≤ (f : ℝ) - 1)]
    have hs0 : 0 < s := by linarith
    have hlog : Real.log (T - 1) ≤ 2 * s := by
      have h1 := Real.log_le_sub_one_of_pos hs0
      have h2 : Real.log s = Real.log (T - 1) / 2 := Real.log_sqrt hy.le
      linarith
    rw [div_le_iff₀ (by linarith)]
    have h3 : (f : ℝ) * Real.log (T - 1) ≤ (f : ℝ) * (2 * s) :=
      mul_le_mul_of_nonneg_left hlog (by linarith)
    nlinarith
  refine ⟨hT2, h4f, ?_, by linarith⟩
  rw [div_le_iff₀ hT0]; linarith
end Formalism.LFunctionChainParameters.SectionsFourToSixTransfer
