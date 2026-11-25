-- Prove2me | solution 1 for Formalism.LFunctionChainParameters.LBrDiv.periodicity_of_text
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-25T17:37:22.122856+00:00
-- url     : https://prove2.me/submissions/d006e82d-46c3-4d03-ba51-3aaab677a52c

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
theorem _root_.solution : PerOfText := by
  intro U0 W Top m f D Pl Emb _ hne logOmτ logOm hT
  refine ⟨fun hM => ?_, fun ρ => hT ρ⟩
  obtain ⟨ρ⟩ := hne
  exact (hM ρ).symm.trans (hT ρ)
end Formalism.LFunctionChainParameters.LBrDiv
