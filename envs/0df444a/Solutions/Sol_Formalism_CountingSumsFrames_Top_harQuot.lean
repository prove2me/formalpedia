-- Prove2me | solution 1 for Formalism.CountingSumsFrames.Top.harQuot
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-25T01:44:31.375705+00:00
-- url     : https://prove2.me/submissions/d4f59725-acde-496a-9b82-1f93d8606ae5

import Definitions.Def_Formalism_PolynomialDimension_MultinomialDepth_PairingAdjointLaplacianHolds
import Definitions.Def_Formalism_PolynomialDimension_MultinomialDepth_HarmonicDecompositionHolds
import Definitions.Def_Formalism_PolynomialDimension_MultinomialDepth_DiagLaplacianDivPowMemSqrtFockLattice
import Definitions.Def_Formalism_PolynomialDimension_MultinomialDepth_SqrtFockGaussLatticeComparisonHolds
import Definitions.Def_Formalism_PolynomialDimension_FinalHar
import Theorems.Thm_Formalism_CountingSumsFrames_harmonicQuotient_holds


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
theorem _root_.solution : Formalism.CountingSumsFrames.HarQuot := Formalism.CountingSumsFrames.harmonicQuotient_holds
end Formalism.CountingSumsFrames.Top
