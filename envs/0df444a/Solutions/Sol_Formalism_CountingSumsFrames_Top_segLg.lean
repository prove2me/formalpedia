-- Prove2me | solution 1 for Formalism.CountingSumsFrames.Top.segLg
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-25T16:19:35.577402+00:00
-- url     : https://prove2.me/submissions/6274eec0-265a-446f-9f9e-d900a172c9f4

import Definitions.Def_Formalism_PolynomialDimension_MultinomialDepth_SegmentHypOfIntervalHyp
import Definitions.Def_Formalism_PolynomialDimension_MultinomialDepth_SegmentTopRoomPublished
import Definitions.Def_Formalism_PolynomialDimension_MultinomialDepth_SegmentBoundThreeHolds
import Definitions.Def_Formalism_PolynomialDimension_ChangeLatticeGoodRank
import Theorems.Thm_Formalism_CountingSumsFrames_segment_log_bound


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
theorem _root_.solution : Formalism.CountingSumsFrames.SegLg := Formalism.CountingSumsFrames.segment_log_bound
end Formalism.CountingSumsFrames.Top
