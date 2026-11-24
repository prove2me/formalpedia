-- Prove2me | solution 1 for Formalism.LFunctionChainParameters.SectionsFourToSixTransfer.level_lower_of_count
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-24T11:05:58.586644+00:00
-- url     : https://prove2.me/submissions/096d2f97-3f08-4419-8fa4-6904ad253ea8

import Definitions.Def_Formalism_SizeWindowBrackets_TranslateWordBoundHypotheses
import Definitions.Def_Formalism_SizeWindowBrackets_ChainSlopeWindows_LevelOfCongruence
import Definitions.Def_Formalism_SizeWindowBrackets_ChainSlopeWindows_SubThreeMulLogTwoLe
import Definitions.Def_Formalism_LogVandermondeBounds_HookGammaAmgmMultinomialBounds
import Definitions.Def_Formalism_SizeWindowBrackets_ChainSlopeWindows_SecondPriceSumWeightsUncovered
import Theorems.Thm_Formalism_LFunctionChainParameters_SectionsFourToSixTransfer_logT_of_window

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
theorem _root_.solution : LevelLowerOfCount := by
  intro U0 W Top m f D c5 Gam X hW h5 hLW hw hlg hmk hL1 hcm u0 u
  obtain ⟨hl, _⟩ := logT_of_window hW hLW u0 u
  obtain ⟨hc, hf, hk, hG, hlG, hG1, hL, hLLa, hLa, hmL, hlk⟩ := hW
  have hk0 : 0 < D.k := by linarith
  have hm : (0 : ℝ) ≤ (m : ℝ) := Nat.cast_nonneg _
  have h1 := (h5 u0 u).1
  have hs : 0 ≤ ∑ j : Fin m, (1 / (f : ℝ)) * ∑ ρ : Fin f, Real.log (D.w u0 j ρ * D.v / π) :=
    Finset.sum_nonneg (fun j _ => mul_nonneg (by positivity)
      (Finset.sum_nonneg (fun ρ _ => Real.log_nonneg (hw u0 j ρ))))
  have hmc : 16 * ((m : ℝ) * D.L) ≤ mainCount D u0 := by
    unfold mainCount
    have := mul_le_mul_of_nonneg_left hlg hm
    linarith
  have hq : (m : ℝ) ^ 2 * D.L / D.k ≤ D.L := by
    rw [div_le_iff₀ hk0]
    have := mul_le_mul_of_nonneg_right hmk hL
    linarith
  have hq2 := mul_le_mul_of_nonneg_left hq hc
  have e3 : 2 * D.logGam / ((f : ℝ) * D.k) = 2 * (D.logGam / ((f : ℝ) * D.k)) := by ring
  have hcl : (2 * c5 + 2) * D.L ≤ 15 * (m : ℝ) * D.L := mul_le_mul_of_nonneg_right hcm hL
  have hmL0 : 0 ≤ (m : ℝ) * D.L := mul_nonneg hm hL
  nlinarith
end Formalism.LFunctionChainParameters.SectionsFourToSixTransfer
