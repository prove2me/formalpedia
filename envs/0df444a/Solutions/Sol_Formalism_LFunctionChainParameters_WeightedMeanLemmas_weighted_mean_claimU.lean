-- Prove2me | solution 1 for Formalism.LFunctionChainParameters.WeightedMeanLemmas.weighted_mean_claimU
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-25T01:07:05.102793+00:00
-- url     : https://prove2.me/submissions/e849c18a-dec8-423a-99f3-83ce41ac5ecb

import Definitions.Def_Formalism_SizeWindowBrackets_RealSlopeBoundsSplit
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Ring
import Mathlib.Data.Fintype.BigOperators
import Definitions.Def_Formalism_SizeWindowBrackets_ChainSlopeWindows_WeightedMeanLemmaNeedsDegree
import Theorems.Thm_Formalism_LFunctionChainParameters_WeightedMeanLemmas_weighted_mean_lemma_ge

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Formalism Formalism.LFunctionChainParameters Formalism.LFunctionChainParameters.WeightedMeanLemmas
open Finset
namespace Formalism.LFunctionChainParameters.WeightedMeanLemmas
theorem _root_.solution (ι : Type*) [Fintype ι] [Nonempty ι] : LemmaU ι := by
  intro d muMaxN muN muMaxM muM h dr BE Sg0 hd hdr hS2
  exact weighted_mean_lemma_ge ι d muMaxN muN muMaxM muM h dr BE Sg0 hd hdr
    ⟨hS2.1, fun u => (hS2.2 u).symm.le⟩
end Formalism.LFunctionChainParameters.WeightedMeanLemmas
