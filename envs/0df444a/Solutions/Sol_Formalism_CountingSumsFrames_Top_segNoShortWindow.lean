-- Prove2me | solution 1 for Formalism.CountingSumsFrames.Top.segNoShortWindow
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-25T16:47:00.580472+00:00
-- url     : https://prove2.me/submissions/ce1ad094-3949-42bc-8d44-9a014b295a95

import Definitions.Def_Formalism_PolynomialDimension_MultinomialDepth_SegmentHypOfIntervalHyp
import Definitions.Def_Formalism_PolynomialDimension_MultinomialDepth_SegmentTopRoomPublished
import Definitions.Def_Formalism_PolynomialDimension_MultinomialDepth_SegmentBoundThreeHolds
import Definitions.Def_Formalism_PolynomialDimension_ChangeLatticeGoodRank
import Theorems.Thm_Formalism_CountingSumsFrames_segment_no_short_window


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
theorem _root_.solution : Formalism.CountingSumsFrames.SegNoShortWindow := Formalism.CountingSumsFrames.segment_no_short_window
end Formalism.CountingSumsFrames.Top
