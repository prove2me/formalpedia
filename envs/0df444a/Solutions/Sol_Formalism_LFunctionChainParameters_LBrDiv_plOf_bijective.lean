-- Prove2me | solution 1 for Formalism.LFunctionChainParameters.LBrDiv.plOf_bijective
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-24T10:29:27.964368+00:00
-- url     : https://prove2.me/submissions/e255a9c7-50bf-499b-9109-220324e64f57

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
theorem _root_.solution (K : Type) [Field K] [NumberField K] :
    Function.Bijective (plOf : HeightOneSpectrum (𝓞 K) → slopeLatticeData.FinPl K) := by
  constructor
  · intro w w' h
    have : w.asIdeal = w'.asIdeal := congrArg Subtype.val h
    exact HeightOneSpectrum.ext this
  · intro p
    refine ⟨⟨p.1, p.2.isPrime, ?_⟩, rfl⟩
    exact Ring.ne_bot_of_isMaximal_of_not_isField p.2 (RingOfIntegers.not_isField K)
end Formalism.LFunctionChainParameters.LBrDiv
