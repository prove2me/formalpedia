-- Prove2me | solution 1 for Formalism.LFunctionChainParameters.LBrDiv.construct_divisibility_of_free
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-25T17:39:49.477412+00:00
-- url     : https://prove2.me/submissions/b2317f74-7140-40c0-b3d6-259dc3fad44f

import Definitions.Def_Formalism_SizeWindowBrackets_SBrDiv
import Definitions.Def_Formalism_SizeWindowBrackets_ChainSlopeWindows_LevelOfCongruence
import Definitions.Def_Formalism_SizeWindowBrackets_ChainSlopeWindows_StronglyIrreducible
import Definitions.Def_Formalism_HarderNarasimhan_HarderNarasimhanProofs_DualPl
import Definitions.Def_Formalism_HarderNarasimhan_HarderNarasimhanProofs_SizeMu
import Definitions.Def_Formalism_HarderNarasimhan_HarderNarasimhanProofs_Rerealize
import Definitions.Def_Formalism_SizeWindowBrackets_ChainSlopeWindows_PBrDiv
import Theorems.Thm_Formalism_LFunctionChainParameters_LBrDiv_divisibility_of_free

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
theorem _root_.solution : MkDivOfFree := by
  intro H _ _ _ W _ m G C D ell N TT T2 a w Fm logOm h hp
  exact divisibility_of_free H W TT m _ (mkData G C.cHH D ell N TT T2 a w Fm) C logOm h hp
end Formalism.LFunctionChainParameters.LBrDiv
