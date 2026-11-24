-- Prove2me | solution 1 for Formalism.LFunctionChainParameters.SectionsFourToSixTransfer.proposition_to_count_general
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-24T11:35:56.328406+00:00
-- url     : https://prove2.me/submissions/8b11f081-a259-43e5-98b2-d34c6d14fe2c

import Definitions.Def_Formalism_SizeWindowBrackets_TranslateWordBoundHypotheses
import Definitions.Def_Formalism_SizeWindowBrackets_ChainSlopeWindows_LevelOfCongruence
import Definitions.Def_Formalism_SizeWindowBrackets_ChainSlopeWindows_SubThreeMulLogTwoLe
import Definitions.Def_Formalism_LogVandermondeBounds_HookGammaAmgmMultinomialBounds
import Definitions.Def_Formalism_SizeWindowBrackets_ChainSlopeWindows_SecondPriceSumWeightsUncovered
import Theorems.Thm_Formalism_LFunctionChainParameters_SectionsFourToSixTransfer_fk_pos
import Theorems.Thm_Formalism_LFunctionChainParameters_SectionsFourToSixTransfer_logT_of_window
import Theorems.Thm_Formalism_LFunctionChainParameters_SectionsFourToSixTransfer_proposition_to_log_t_upper

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
theorem _root_.solution : Prop5ToCount := by
  intro U0 W Top m f D C c5 Gam X hW h5 hV hLW hC u0 u
  have hup := proposition_to_log_t_upper D c5 Gam X hW h5 hLW
  obtain ⟨hl, hu⟩ := logT_of_window hW hLW u0 u
  obtain ⟨hy, hy1⟩ := fk_pos hW
  have hW' := hW
  obtain ⟨hc, hf, hk, hG, hlG, hG1, hL, hLLa, hLa, hmL, hlk⟩ := hW
  have hk0 : 0 < D.k := by linarith
  have hq : 0 ≤ D.L + (m : ℝ) ^ 2 * D.L / D.k :=
    add_nonneg hL (div_nonneg (mul_nonneg (sq_nonneg _) hL) hk0.le)
  rw [hC]
  refine ⟨?_, hup u0 u, ?_⟩
  · have := (h5 u0 u).1
    unfold mainCount at this
    have e : (c5 + 1) * (D.L + (m : ℝ) ^ 2 * D.L / D.k)
        = c5 * (D.L + (m : ℝ) ^ 2 * D.L / D.k) + (D.L + (m : ℝ) ^ 2 * D.L / D.k) := by ring
    rw [e]; linarith
  · intro u'
    obtain ⟨hl', hu'⟩ := logT_of_window hW' hLW u0 u'
    have hv := abs_le.mp (hV u0 u u')
    have e : (c5 + 1) * Real.log D.k = c5 * Real.log D.k + Real.log D.k := by ring
    rw [e]
    exact abs_le.mpr ⟨by linarith [hv.1], by linarith [hv.2]⟩
end Formalism.LFunctionChainParameters.SectionsFourToSixTransfer
