-- Prove2me | solution 1 for Formalism.LFunctionChainParameters.SectionsFourToSixTransfer.proposition_to_log_t_upper
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-24T11:05:54.325932+00:00
-- url     : https://prove2.me/submissions/dbdff0b9-7e47-4d6c-8609-e37f6fde4a6f

import Definitions.Def_Formalism_SizeWindowBrackets_TranslateWordBoundHypotheses
import Definitions.Def_Formalism_SizeWindowBrackets_ChainSlopeWindows_LevelOfCongruence
import Definitions.Def_Formalism_SizeWindowBrackets_ChainSlopeWindows_SubThreeMulLogTwoLe
import Definitions.Def_Formalism_LogVandermondeBounds_HookGammaAmgmMultinomialBounds
import Definitions.Def_Formalism_SizeWindowBrackets_ChainSlopeWindows_SecondPriceSumWeightsUncovered
import Theorems.Thm_Formalism_LFunctionChainParameters_SectionsFourToSixTransfer_fk_pos
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
theorem _root_.solution : Prop5ToLogTUp := by
  intro U0 W Top m f D c5 Gam X hW h5 hLW u0 u
  obtain ⟨_, hu⟩ := logT_of_window hW hLW u0 u
  obtain ⟨hy, hy1⟩ := fk_pos hW
  obtain ⟨hc, hf, hk, hG, hlG, hG1, hL, hLLa, hLa, hmL, hlk⟩ := hW
  have hg : 0 ≤ 2 * D.logGam / ((f : ℝ) * D.k) := by
    rw [hlG]; exact div_nonneg (mul_nonneg (by norm_num) (Real.log_nonneg hG)) hy.le
  have := (h5 u0 u).2
  have e : (c5 + 1) * (m : ℝ) * D.L = c5 * (m : ℝ) * D.L + (m : ℝ) * D.L := by ring
  rw [e]; linarith
end Formalism.LFunctionChainParameters.SectionsFourToSixTransfer
