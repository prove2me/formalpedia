-- Prove2me | solution 1 for Formalism.CountingSumsFrames.harmonicQuotient_holds
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-25T01:35:19.11711+00:00
-- url     : https://prove2.me/submissions/f10003ba-fb76-4fcb-bd82-738ac4074a53

import Definitions.Def_Formalism_PolynomialDimension_StatementHar
import Definitions.Def_Formalism_PolynomialDimension_MultinomialDepth_HarmonicDecompositionHolds
import Definitions.Def_Formalism_PolynomialDimension_MultinomialDepth_DiagLaplacianDivPowMemSqrtFockLattice
import Definitions.Def_Formalism_PolynomialDimension_MultinomialDepth_SqrtFockGaussLatticeComparisonHolds
import Theorems.Thm_Formalism_CountingSumsFrames_Har4_harQuot_of
import Theorems.Thm_Formalism_CountingSumsFrames_gaussLatticeProjection_holds
import Theorems.Thm_Formalism_CountingSumsFrames_harmonicProjection_holds


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open scoped BigOperators
open Finset MvPolynomial
open Formalism Formalism.CountingSumsFrames
namespace Formalism.CountingSumsFrames
theorem _root_.solution : HarQuot := Har4.harQuot_of harmonicProjection_holds gaussLatticeProjection_holds
end Formalism.CountingSumsFrames
