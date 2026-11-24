-- Prove2me | solution 1 for Formalism.LFunctionChainParameters.SectionsFourToSixTransfer.z_terms
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-24T10:46:56.629686+00:00
-- url     : https://prove2.me/submissions/bcc7b584-7745-4ba8-a1b1-3277d4e502f8

import Definitions.Def_Formalism_SizeWindowBrackets_TranslateWordBoundHypotheses
import Definitions.Def_Formalism_SizeWindowBrackets_ChainSlopeWindows_LevelOfCongruence
import Definitions.Def_Formalism_SizeWindowBrackets_ChainSlopeWindows_SubThreeMulLogTwoLe
import Definitions.Def_Formalism_LogVandermondeBounds_HookGammaAmgmMultinomialBounds
import Definitions.Def_Formalism_SizeWindowBrackets_ChainSlopeWindows_SecondPriceSumWeightsUncovered
import Theorems.Thm_Formalism_LFunctionChainParameters_SectionsFourToSixTransfer_nT_nonneg
import Theorems.Thm_Formalism_LFunctionChainParameters_SectionsFourToSixTransfer_zTerms_real
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
theorem _root_.solution : ZTerms := by
  intro U0 W Top _ m f D cZ cL cU Sc LZ logT hW hT
  obtain ⟨hcZ, hcL, hcU, ha, hk, hmk, hb', hSc, haT, hL, hLLa, hlk, hlkv, hLZ, hw1, hw2⟩ := hW
  have hk0 : 0 < D.k := by linarith
  have hn := nT_nonneg D
  have hs0 : 0 ≤ ∑ t, D.aT t / D.k := Finset.sum_nonneg (fun t _ => div_nonneg (haT t).1 hk0.le)
  have hs1 : ∑ t, D.aT t / D.k ≤ D.nT * (2 * D.a / D.k) := by
    have : ∑ t, D.aT t / D.k ≤ ∑ _t : Top, 2 * D.a / D.k :=
      Finset.sum_le_sum (fun t _ => div_le_div_of_nonneg_right (haT t).2 hk0.le)
    simpa [Data.nT, Finset.sum_const, nsmul_eq_mul] using this
  unfold unitZ
  exact zTerms_real hcZ hcL hcU ha hk hmk hb' hSc hL hLLa hlk hlkv hLZ hw1 hw2 hn
    (Nat.cast_nonneg _) (Nat.cast_nonneg _) hs0 hs1 hT
end Formalism.LFunctionChainParameters.SectionsFourToSixTransfer
