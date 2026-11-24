-- Prove2me | solution 1 for Formalism.RankGapBounds.V4.tops_lemma_sixteen_holds
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-24T11:59:03.447637+00:00
-- url     : https://prove2.me/submissions/96a3f514-bd9f-4215-97b6-a332f30b69e4

import Definitions.Def_Formalism_RankGapBounds_GridNumericalHypotheses
import Definitions.Def_Formalism_RankGapBounds_RankGapProofs_RandomSubsetLemmaCounterexample
import Definitions.Def_Formalism_RankGapBounds_RankGapProofs_RankGapDecayHypothesis
import Theorems.Thm_Formalism_RankGapBounds_LocalQuadraticParts_tops_lemma_six_holds


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Formalism Formalism.RankGapBounds Formalism.RankGapBounds.V4
open Formalism.RankGapBounds.LocalQuadraticParts Formalism.RankGapBounds.ExistsSmulMemTer
namespace Formalism.RankGapBounds.V4
theorem _root_.solution : RankGapPrintedLemma := by
  intro α ι _ _ _ δ β ω BAD _ hδ0 hδ1 hq hβ hω hBAD
  exact tops_lemma_six_holds α ι δ β ω BAD hδ0 hδ1 (by linarith) hβ hω hBAD
end Formalism.RankGapBounds.V4
