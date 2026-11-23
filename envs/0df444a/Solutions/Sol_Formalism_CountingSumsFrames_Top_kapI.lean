-- Prove2me | solution 1 for Formalism.CountingSumsFrames.Top.kapI
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T13:54:39.567427+00:00
-- url     : https://prove2.me/submissions/80a260da-43a9-46b8-a882-43a38beb6532

import Definitions.Def_Formalism_PolynomialDimension_MultinomialDepth_SecondParameterSizeBoundsHolds
import Definitions.Def_Formalism_PolynomialDimension_MultinomialDepth_SecondParameterSlackBoundsHolds
import Definitions.Def_Formalism_PolynomialDimension_MultinomialDepth_FrameMultinomialBoundHolds
import Definitions.Def_Formalism_PolynomialDimension_MultinomialDepth_ParamsI
import Definitions.Def_Formalism_PolynomialDimension_MultinomialDepth_IntervalCleanDepthBound
import Definitions.Def_Formalism_PolynomialDimension_FinalNum
import Theorems.Thm_Formalism_CountingSumsFrames_interval_kappa_bound


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
theorem _root_.solution : Formalism.CountingSumsFrames.KapI := Formalism.CountingSumsFrames.interval_kappa_bound
end Formalism.CountingSumsFrames.Top
