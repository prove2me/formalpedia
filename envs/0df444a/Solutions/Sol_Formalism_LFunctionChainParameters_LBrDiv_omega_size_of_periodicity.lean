-- Prove2me | solution 1 for Formalism.LFunctionChainParameters.LBrDiv.omega_size_of_periodicity
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-25T17:17:30.647709+00:00
-- url     : https://prove2.me/submissions/f616d72b-3f38-43e1-ada5-70802e157aa8

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
theorem _root_.solution : OmSizeOfPer := by
  intro U0 W Top m f D logOm A B hp hg hA hB hL
  have hp' : logOm = D.gam + Real.log (Real.pi / D.v) - D.LpL := hp
  rw [hp']
  have h1 := abs_le.mp hg
  have h2 := abs_le.mp hA
  have h3 := abs_le.mp hB
  exact abs_le.mpr ⟨by linarith [h1.1, h2.1, h3.2], by linarith [h1.2, h2.2, h3.1]⟩
end Formalism.LFunctionChainParameters.LBrDiv
