-- Prove2me | solution 1 for Formalism.CountingSumsFrames.Top.segDepth
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-25T16:21:24.434197+00:00
-- url     : https://prove2.me/submissions/b1a44248-d7c3-4189-981b-bd7e538d4a3c

import Definitions.Def_Formalism_PolynomialDimension_MultinomialDepth_SegmentHypOfIntervalHyp
import Definitions.Def_Formalism_PolynomialDimension_MultinomialDepth_SegmentTopRoomPublished
import Definitions.Def_Formalism_PolynomialDimension_MultinomialDepth_SegmentBoundThreeHolds
import Definitions.Def_Formalism_PolynomialDimension_ChangeLatticeGoodRank
import Theorems.Thm_Formalism_CountingSumsFrames_segment_depth_bound


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
theorem _root_.solution : Formalism.CountingSumsFrames.SegDepth := Formalism.CountingSumsFrames.segment_depth_bound
end Formalism.CountingSumsFrames.Top
