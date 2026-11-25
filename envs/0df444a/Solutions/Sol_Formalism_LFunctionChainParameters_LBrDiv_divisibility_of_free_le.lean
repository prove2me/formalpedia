-- Prove2me | solution 1 for Formalism.LFunctionChainParameters.LBrDiv.divisibility_of_free_le
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-25T17:16:57.913012+00:00
-- url     : https://prove2.me/submissions/10e90d19-3fa5-44c5-904b-4d00a9b91c1f

import Definitions.Def_Formalism_SizeWindowBrackets_SBrDiv
import Definitions.Def_Formalism_SizeWindowBrackets_ChainSlopeWindows_LevelOfCongruence
import Definitions.Def_Formalism_SizeWindowBrackets_ChainSlopeWindows_StronglyIrreducible
import Definitions.Def_Formalism_HarderNarasimhan_HarderNarasimhanProofs_DualPl
import Definitions.Def_Formalism_HarderNarasimhan_HarderNarasimhanProofs_SizeMu
import Definitions.Def_Formalism_HarderNarasimhan_HarderNarasimhanProofs_Rerealize
import Definitions.Def_Formalism_SizeWindowBrackets_ChainSlopeWindows_PBrDiv
import Theorems.Thm_Formalism_LFunctionChainParameters_LBrDiv_divisibility_free_shift

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
theorem _root_.solution : DivOfFreeLe := by
  intro U0 W Top _ m f D C logOm ha h hp
  have h2 := (divisibility_free_shift U0 W Top m f D C logOm D.logOm).mp h
  intro u0 u
  have h3 := h2 u0 u
  have hs : 0 ≤ D.sumA := Finset.sum_nonneg fun t _ => ha t
  have hle : D.logOm - logOm ≤ 0 := by
    have : D.logOm ≤ logOm := hp
    linarith
  have hm : 0 ≤ (m : ℝ) * D.sumA := mul_nonneg (Nat.cast_nonneg m) hs
  have : (m : ℝ) * D.sumA * (D.logOm - logOm) ≤ 0 := mul_nonpos_of_nonneg_of_nonpos hm hle
  linarith
end Formalism.LFunctionChainParameters.LBrDiv
