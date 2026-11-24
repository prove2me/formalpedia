-- Prove2me | solution 1 for Formalism.LFunctionChainParameters.SectionsFourToSixTransfer.proposition_to_count
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-24T11:46:01.382136+00:00
-- url     : https://prove2.me/submissions/e70f61a7-fd64-42a9-91e3-fff8239885d9

import Definitions.Def_Formalism_SizeWindowBrackets_TranslateWordBoundHypotheses
import Definitions.Def_Formalism_SizeWindowBrackets_ChainSlopeWindows_LevelOfCongruence
import Definitions.Def_Formalism_SizeWindowBrackets_ChainSlopeWindows_SubThreeMulLogTwoLe
import Definitions.Def_Formalism_LogVandermondeBounds_HookGammaAmgmMultinomialBounds
import Definitions.Def_Formalism_SizeWindowBrackets_ChainSlopeWindows_SecondPriceSumWeightsUncovered
import Theorems.Thm_Formalism_LFunctionChainParameters_SectionsFourToSixTransfer_proposition_to_count_general

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
theorem _root_.solution : Prop5ToCount5 := by
  intro U0 W Top m f D C c5 Gam X hW h5 hV hLW hC
  have hCount : D.Count { C with cCount := c5 + 1 } :=
    proposition_to_count_general D { C with cCount := c5 + 1 } c5 Gam X hW h5 hV hLW rfl
  obtain ⟨hc, hf, hk, hG, hlG, hG1, hL, hLLa, hLa, hmL, hlk⟩ := hW
  have hk0 : 0 < D.k := by linarith
  have hq0 : 0 ≤ (m : ℝ) ^ 2 / D.k := div_nonneg (sq_nonneg _) hk0.le
  have e1 : (m : ℝ) ^ 2 * D.L / D.k = (m : ℝ) ^ 2 / D.k * D.L := by ring
  have e2 : (m : ℝ) ^ 2 * D.La / D.k = (m : ℝ) ^ 2 / D.k * D.La := by ring
  have e3 : 2 * D.logGam / ((f : ℝ) * D.k) = 2 * (D.logGam / ((f : ℝ) * D.k)) := by ring
  have hmL' : (m : ℝ) ^ 2 / D.k * D.L ≤ (m : ℝ) ^ 2 / D.k * D.La := mul_le_mul_of_nonneg_left hLLa hq0
  have hmLa : 0 ≤ (m : ℝ) ^ 2 / D.k * D.La := mul_nonneg hq0 (by linarith)
  have hq : 0 ≤ D.La + (m : ℝ) ^ 2 / D.k * D.La := by linarith
  have hsum : D.L + (m : ℝ) ^ 2 / D.k * D.L ≤ D.La + (m : ℝ) ^ 2 / D.k * D.La := by linarith
  have hcs := mul_le_mul_of_nonneg_left hsum (by linarith : 0 ≤ c5 + 1)
  intro u0 u
  obtain ⟨h1, h2, h3⟩ := hCount u0 u
  refine ⟨?_, ?_, ?_⟩
  · have h1' : _ - (c5 + 1) * (D.L + (m : ℝ) ^ 2 * D.L / D.k) - 2 * D.logGam / ((f : ℝ) * D.k) ≤ _ := h1
    rw [e1, e3] at h1'
    rw [e2]
    have := mul_le_mul_of_nonneg_right hC hq
    have e4 : (c5 + 3) * (D.La + (m : ℝ) ^ 2 / D.k * D.La)
        = (c5 + 1) * (D.La + (m : ℝ) ^ 2 / D.k * D.La) + 2 * (D.La + (m : ℝ) ^ 2 / D.k * D.La) := by ring
    linarith
  · have h2' : _ ≤ (c5 + 1) * (m : ℝ) * D.L := h2
    have := mul_le_mul_of_nonneg_right (by linarith : c5 + 1 ≤ C.cCount) (by linarith : 0 ≤ (m : ℝ) * D.L)
    linarith
  · intro u'
    have h3' : _ ≤ (c5 + 1) * Real.log D.k := h3 u'
    have := mul_le_mul_of_nonneg_right (by linarith : c5 + 1 ≤ C.cCount) (by linarith : 0 ≤ Real.log D.k)
    linarith
end Formalism.LFunctionChainParameters.SectionsFourToSixTransfer
