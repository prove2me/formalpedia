-- Prove2me | solution 1 for Formalism.LFunctionChainParameters.LChain6.words_of_count
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-25T05:14:29.686664+00:00
-- url     : https://prove2.me/submissions/cbeb52b8-92b5-41bc-b342-b3fe126df012

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
theorem _root_.solution : WordsOfCount := by
  intro X Gam T k dst Dstar d C0S f hX hG hf hk hT h4 hdst hD hXD hd hC
  have hf' : (1 : ℝ) ≤ (f : ℝ) := by exact_mod_cast hf
  have hG0 : 0 < Gam := by linarith
  have hy : 0 < (f : ℝ) * k := by positivity
  have hT0 : 0 < T := by linarith
  have hT1 : 1 ≤ T := by linarith
  have hGp : 0 < Gam ^ (-(2 / ((f : ℝ) * k))) := Real.rpow_pos_of_pos hG0 _
  have e1 : (X * Gam ^ (-(2 / ((f : ℝ) * k)))) ^ ((f : ℝ) * k) = Dstar / dst * Gam ^ (-2 : ℝ) := by
    rw [Real.mul_rpow hX.le hGp.le, hXD, ← Real.rpow_mul hG0.le]
    congr 2
    field_simp
  have e2 : Dstar / dst * Gam ^ (-2 : ℝ) ≤ T ^ ((f : ℝ) * k) := by
    rw [← e1]
    exact Real.rpow_le_rpow (mul_pos hX hGp).le hT hy.le
  have hz : T ≤ T ^ k := by
    calc T = T ^ (1 : ℝ) := (Real.rpow_one T).symm
      _ ≤ T ^ k := Real.rpow_le_rpow_of_exponent_le hT1 hk
  set z : ℝ := T ^ k with hzdef
  have hz0 : 0 < z := by linarith
  have e3 : z ^ f = T ^ ((f : ℝ) * k) := by
    rw [hzdef, ← Real.rpow_natCast, ← Real.rpow_mul hT0.le, mul_comm]
  have hfz : (f : ℝ) / z ≤ 1 / 4 := by
    rw [div_le_iff₀ hz0]; linarith
  have e4 : (z - 1) ^ f = z ^ f * (1 + -(1 / z)) ^ f := by
    rw [← mul_pow]; congr 1; field_simp; ring
  have hinv : 1 / z ≤ 1 := by
    rw [div_le_one hz0]; linarith
  have e5 : 1 + (f : ℝ) * -(1 / z) ≤ (1 + -(1 / z)) ^ f := one_add_mul_le_pow (by linarith) f
  have e6 : 3 / 4 ≤ (1 + -(1 / z)) ^ f := by
    have : (f : ℝ) * -(1 / z) = -((f : ℝ) / z) := by ring
    linarith
  have e7 : 3 / 4 * z ^ f ≤ (z - 1) ^ f := by
    rw [e4]
    have := pow_pos hz0 f
    nlinarith
  have e8 : Gam ^ (-2 : ℝ) = 1 / Gam ^ 2 := by
    rw [Real.rpow_neg hG0.le, show (2 : ℝ) = ((2 : ℕ) : ℝ) by norm_num, Real.rpow_natCast, one_div]
  have e9 : 3 / 4 * (Dstar / Gam ^ 2) ≤ d := by
    rw [hd]
    have h1 : dst * (3 / 4 * (Dstar / dst * Gam ^ (-2 : ℝ))) ≤ dst * (z - 1) ^ f := by
      apply mul_le_mul_of_nonneg_left _ hdst.le
      rw [e3] at e7
      linarith
    have h2 : dst * (3 / 4 * (Dstar / dst * Gam ^ (-2 : ℝ))) = 3 / 4 * (Dstar / Gam ^ 2) := by
      rw [e8]; field_simp
    linarith
  have hq : 0 < Dstar / Gam ^ 2 := by positivity
  have e10 : Dstar / Gam ^ 2 / C0S ≤ Dstar / Gam ^ 2 / 2 := div_le_div_of_nonneg_left hq.le (by norm_num) hC
  linarith
end Formalism.LFunctionChainParameters.LChain6
