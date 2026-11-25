-- Prove2me | solution 1 for Formalism.CountingSumsFrames.Top.hypSegOfHypI
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-25T16:26:36.259295+00:00
-- url     : https://prove2.me/submissions/74b29449-f9ce-45f1-93ef-562168dda337

import Definitions.Def_Formalism_PolynomialDimension_MultinomialDepth_SegmentHypOfIntervalHyp
import Definitions.Def_Formalism_PolynomialDimension_MultinomialDepth_SegmentTopRoomPublished
import Definitions.Def_Formalism_PolynomialDimension_MultinomialDepth_SegmentBoundThreeHolds
import Definitions.Def_Formalism_PolynomialDimension_ChangeLatticeGoodRank
import Theorems.Thm_Formalism_CountingSumsFrames_segment_hyp_of_interval_hyp


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Formalism Formalism.CountingSumsFrames Formalism.CountingSumsFrames.Top
namespace Formalism.CountingSumsFrames.Top
theorem _root_.solution : Formalism.CountingSumsFrames.HypSegOfHypI := Formalism.CountingSumsFrames.segment_hyp_of_interval_hyp
end Formalism.CountingSumsFrames.Top
