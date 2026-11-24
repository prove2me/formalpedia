-- Prove2me | solution 1 for Formalism.LFunctionChainParameters.LBrDiv.periodicity_solvable
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-24T10:29:26.67622+00:00
-- url     : https://prove2.me/submissions/2df248a7-f4d1-4ac8-a7d8-d8583dbc61d5

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
theorem _root_.solution : PerSolvable := by
  intro gam LpL logOm
  refine ⟨Real.pi * Real.exp (gam - LpL - logOm), mul_pos Real.pi_pos (Real.exp_pos _), ?_⟩
  rw [Real.log_div Real.pi_pos.ne' (mul_pos Real.pi_pos (Real.exp_pos _)).ne',
    Real.log_mul Real.pi_pos.ne' (Real.exp_pos _).ne', Real.log_exp]
  ring
end Formalism.LFunctionChainParameters.LBrDiv
