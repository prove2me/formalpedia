-- Prove2me | solution 1 for Formalism.CountingSumsFrames.Top.cleanArith
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T10:44:00.585901+00:00
-- url     : https://prove2.me/submissions/ffaad284-289e-48dc-8f6c-31cbb87bca48

import Definitions.Def_Formalism_PolynomialDimension_MultinomialDepth_ExistsNonzeroExchangedMinorHolds
import Definitions.Def_Formalism_PolynomialDimension_MultinomialDepth_FrobeniusDetVanishingHolds
import Definitions.Def_Formalism_PolynomialDimension_MultinomialDepth_FockGaussComparisonHolds
import Definitions.Def_Formalism_PolynomialDimension_DetMulEqSumAdjugate

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
theorem _root_.solution : Formalism.CountingSumsFrames.CleanArith := by
  refine ⟨fun j v o e' Q h1 h2 h3 => by nlinarith, fun e c' Q h => ⟨by nlinarith, by omega⟩⟩
end Formalism.CountingSumsFrames.Top
