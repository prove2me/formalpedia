-- Prove2me | solution 1 for Formalism.CountingSumsFrames.Top.shareProd
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T14:01:00.982965+00:00
-- url     : https://prove2.me/submissions/1c8dd418-29f1-4907-9003-40aaf0ac43ee

import Definitions.Def_Formalism_PolynomialDimension_MultinomialDepth_DvdPowOfNotPowSuccDvd
import Definitions.Def_Formalism_PolynomialDimension_MultinomialDepth_FockGaussComparisonHolds
import Mathlib
import Definitions.Def_Formalism_PolynomialDimension_MultinomialDepth_IntervalRoomBound
import Definitions.Def_Formalism_PolynomialDimension_MultinomialKLog
import Theorems.Thm_Formalism_CountingSumsFrames_share_product_bound


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
theorem _root_.solution : Formalism.CountingSumsFrames.ShareProd := Formalism.CountingSumsFrames.share_product_bound
end Formalism.CountingSumsFrames.Top
