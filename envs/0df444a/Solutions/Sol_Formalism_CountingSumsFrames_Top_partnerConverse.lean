-- Prove2me | solution 1 for Formalism.CountingSumsFrames.Top.partnerConverse
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-25T16:21:20.949195+00:00
-- url     : https://prove2.me/submissions/610ac727-57e3-47da-ba31-ebb983231ac4

import Definitions.Def_Formalism_PolynomialDimension_MultinomialDepth_SegmentHypOfIntervalHyp
import Definitions.Def_Formalism_PolynomialDimension_MultinomialDepth_SegmentTopRoomPublished
import Definitions.Def_Formalism_PolynomialDimension_MultinomialDepth_SegmentBoundThreeHolds
import Definitions.Def_Formalism_PolynomialDimension_ChangeLatticeGoodRank
import Theorems.Thm_Formalism_CountingSumsFrames_partner_converse


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
theorem _root_.solution : Formalism.CountingSumsFrames.PartnerConverse := Formalism.CountingSumsFrames.partner_converse
end Formalism.CountingSumsFrames.Top
