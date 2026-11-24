-- Prove2me | solution 1 for Formalism.LFunctionChainParameters.SectionsFourToSixTransfer.z_to_slopes
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-24T11:05:59.253951+00:00
-- url     : https://prove2.me/submissions/0e57f6bb-616f-4fc8-a4cd-a976775fc815

import Definitions.Def_Formalism_SizeWindowBrackets_TranslateWordBoundHypotheses
import Definitions.Def_Formalism_SizeWindowBrackets_ChainSlopeWindows_LevelOfCongruence
import Definitions.Def_Formalism_SizeWindowBrackets_ChainSlopeWindows_SubThreeMulLogTwoLe
import Definitions.Def_Formalism_LogVandermondeBounds_HookGammaAmgmMultinomialBounds
import Definitions.Def_Formalism_SizeWindowBrackets_ChainSlopeWindows_SecondPriceSumWeightsUncovered
import Theorems.Thm_Formalism_LFunctionChainParameters_SectionsFourToSixTransfer_nT_nonneg
import Theorems.Thm_Formalism_LFunctionChainParameters_SectionsFourToSixTransfer_z_terms
import Theorems.Thm_Formalism_RankGapBounds_WeightedMeanData_Data_nT_nonneg


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
theorem _root_.solution : ZToSlopes := by
  intro U0 W Top _ m f D C cZ cL cU Sc LZ hW hT hZ hC u0 u
  obtain ⟨t1, t2, t3, t4, t5, t6, t7, t8⟩ := z_terms D cZ cL cU Sc LZ _ hW (hT u0 u)
  obtain ⟨hcZ, hcL, hcU, ha, hk, hmk, hb', hSc, haT, hL, hLLa, hlk, hlkv, hLZ, hw1, hw2⟩ := hW
  have hk0 : 0 < D.k := by linarith
  have hU : 0 ≤ unitZ D := mul_nonneg (mul_nonneg (nT_nonneg D) ha) (le_trans hL hLLa)
  have hmk' : 0 ≤ (m : ℝ) / D.k := div_nonneg (Nat.cast_nonneg _) hk0.le
  have hUm : 0 ≤ unitZ D * ((m : ℝ) / D.k) := mul_nonneg hU hmk'
  obtain ⟨z1, z2⟩ := hZ u0 u
  have e1 : C.cSlope * D.nT * D.a * D.La * (1 + (m : ℝ) / D.k)
      = C.cSlope * unitZ D + C.cSlope * (unitZ D * ((m : ℝ) / D.k)) := by unfold unitZ; ring
  have e2 : C.cSlope * D.nT * D.a * D.La = C.cSlope * unitZ D := by unfold unitZ; ring
  have hC1 := mul_le_mul_of_nonneg_right hC hU
  have hC2 := mul_le_mul_of_nonneg_right hC hUm
  unfold cSlopeZ at hC1 hC2
  have p1 : 0 ≤ cZ * cU * unitZ D := mul_nonneg (mul_nonneg hcZ hcU) hU
  have p2 : 0 ≤ cU * unitZ D := mul_nonneg hcU hU
  have p3 : 0 ≤ cZ * unitZ D := mul_nonneg hcZ hU
  have p4 : 0 ≤ cZ * cL * unitZ D := mul_nonneg (mul_nonneg hcZ hcL) hU
  have q3 : 0 ≤ cZ * (unitZ D * ((m : ℝ) / D.k)) := mul_nonneg hcZ hUm
  have q4 : 0 ≤ cZ * cL * (unitZ D * ((m : ℝ) / D.k)) := mul_nonneg (mul_nonneg hcZ hcL) hUm
  constructor
  · rw [e1]
    unfold ZiiR at z1
    linarith
  · rw [e2]
    unfold ZiiiR at z2
    have e3 : cZ * (f : ℝ) * (D.b' + Sc) * (D.k * Real.log (D.k * D.v) + Real.log (D.T u0 u))
        = cZ * (f : ℝ) * (D.b' + Sc) * (D.k * Real.log (D.k * D.v))
          + cZ * (f : ℝ) * (D.b' + Sc) * Real.log (D.T u0 u) := by ring
    linarith
end Formalism.LFunctionChainParameters.SectionsFourToSixTransfer
