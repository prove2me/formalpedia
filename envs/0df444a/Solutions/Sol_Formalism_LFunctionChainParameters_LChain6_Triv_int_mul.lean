-- Prove2me | solution 1 for Formalism.LFunctionChainParameters.LChain6.Triv.int_mul
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-25T17:17:14.428701+00:00
-- url     : https://prove2.me/submissions/fe211709-2dc2-46b3-9c9b-f0f225f8a1f0

import Definitions.Def_Formalism_SizeWindowBrackets_SlopesFromSizeAndCount
import Definitions.Def_Formalism_SizeWindowBrackets_ChainSlopeWindows_ChainLatticeSizesModelEventually
import Definitions.Def_Formalism_SizeWindowBrackets_ChainSlopeWindows_PBrDiv
import Definitions.Def_Formalism_SizeWindowBrackets_ChainSlopeWindows_ChainAnalyticVariantOfTop

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Module NumberField Matrix IsDedekindDomain
open Formalism.HN
noncomputable section
open Formalism Formalism.LFunctionChainParameters Formalism.LFunctionChainParameters.LChain6 Formalism.LFunctionChainParameters.LChain6.Triv
open Formalism Formalism.D5 Formalism.RankGapBounds.WeightedMeanData Formalism.LFunctionChainParameters.WeightedSlopeBounds Formalism.LFunctionChainParameters.characterSumData Formalism.LFunctionChainParameters.ThickSetMeanBounds Formalism.LFunctionChainParameters.LErr Formalism.LFunctionChainParameters.LChain
  Formalism.LFunctionChainParameters.LChain2 Formalism.LFunctionChainParameters.LHost Formalism.LFunctionChainParameters.LBr2 Formalism.LFunctionChainParameters.LBrDiv Formalism.LFunctionChainParameters.SectionsFourToSixTransfer Formalism.LFunctionChainParameters.LChain6
open Formalism.LFunctionChainParameters.ProjectiveLineModels (stdLat inclMat)
variable (K : Type) [Field K] [NumberField K] [StarRing K] [IsTotallyComplex K]
namespace Formalism.LFunctionChainParameters.LChain6.Triv
theorem _root_.solution {a c : K} (ha : a ∈ Set.range (algebraMap (𝓞 K) K)) (hc : c ∈ Set.range (algebraMap (𝓞 K) K)) :
    a * c ∈ Set.range (algebraMap (𝓞 K) K) := by
  obtain ⟨a', rfl⟩ := ha
  obtain ⟨c', rfl⟩ := hc
  exact ⟨a' * c', by simp⟩
end Formalism.LFunctionChainParameters.LChain6.Triv
