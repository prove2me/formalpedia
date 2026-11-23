-- Prove2me | solution 1 for Formalism.CountingSumsFrames.Top.paramsII0
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T14:06:56.141771+00:00
-- url     : https://prove2.me/submissions/0278fc80-68cc-48bc-b3e0-d57aa7566c2d

import Definitions.Def_Formalism_PolynomialDimension_MultinomialDepth_SecondParameterSizeBoundsHolds
import Definitions.Def_Formalism_PolynomialDimension_MultinomialDepth_SecondParameterSlackBoundsHolds
import Definitions.Def_Formalism_PolynomialDimension_MultinomialDepth_FrameMultinomialBoundHolds
import Definitions.Def_Formalism_PolynomialDimension_MultinomialDepth_ParamsI
import Definitions.Def_Formalism_PolynomialDimension_MultinomialDepth_IntervalCleanDepthBound
import Definitions.Def_Formalism_PolynomialDimension_FinalNum
import Theorems.Thm_Formalism_CountingSumsFrames_secondParameterSizeBounds_holds


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
theorem _root_.solution : Formalism.CountingSumsFrames.ParamsII0 := Formalism.CountingSumsFrames.secondParameterSizeBounds_holds
end Formalism.CountingSumsFrames.Top
