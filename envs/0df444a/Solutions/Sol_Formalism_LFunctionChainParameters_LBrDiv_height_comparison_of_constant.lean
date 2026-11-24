-- Prove2me | solution 1 for Formalism.LFunctionChainParameters.LBrDiv.height_comparison_of_constant
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-24T10:28:39.521187+00:00
-- url     : https://prove2.me/submissions/0f7efc3b-7e70-4807-b8bc-96694a6c9fbf

import Definitions.Def_Formalism_SizeWindowBrackets_SBrDiv
import Definitions.Def_Formalism_SizeWindowBrackets_ChainSlopeWindows_LevelOfCongruence
import Definitions.Def_Formalism_SizeWindowBrackets_ChainSlopeWindows_StronglyIrreducible
import Definitions.Def_Formalism_HarderNarasimhan_HarderNarasimhanProofs_DualPl
import Definitions.Def_Formalism_HarderNarasimhan_HarderNarasimhanProofs_SizeMu
import Definitions.Def_Formalism_HarderNarasimhan_HarderNarasimhanProofs_Rerealize
import Definitions.Def_Formalism_SizeWindowBrackets_ChainSlopeWindows_PBrDiv

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Module NumberField IsDedekindDomain
open Formalism.HN
noncomputable section
open Formalism Formalism.LFunctionChainParameters Formalism.LFunctionChainParameters.LBrDiv
open Formalism Formalism.D5 Formalism.RankGapBounds.WeightedMeanData Formalism.LFunctionChainParameters.WeightedSlopeBounds Formalism.LFunctionChainParameters.characterSumData Formalism.LFunctionChainParameters.LErr Formalism.LFunctionChainParameters.LChain2
namespace Formalism.LFunctionChainParameters.LBrDiv
theorem _root_.solution : HeightVariationOfCorrectedHeightBound := by
  intro U0 W Top _ m f D C C0 Pl e aP haP hC ha hLa hB h u0 u u'
  have h1 := h u0 u u'
  rw [Finset.sum_map, Finset.sum_map, Finset.card_map, Finset.card_univ] at h1
  simp only [haP] at h1
  have hX : 0 ≤ (Fintype.card Top : ℝ) * D.a * D.La + (m : ℝ) * D.B0 :=
    add_nonneg (mul_nonneg (mul_nonneg (Nat.cast_nonneg _) ha) hLa) (mul_nonneg (Nat.cast_nonneg _) hB)
  exact h1.trans (mul_le_mul_of_nonneg_right hC hX)
end Formalism.LFunctionChainParameters.LBrDiv
