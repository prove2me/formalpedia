-- Prove2me | solution 1 for Formalism.CountingSumsFrames.gaussLatticeProjectionExponent_holds
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-25T16:19:32.929806+00:00
-- url     : https://prove2.me/submissions/fa2dc2ff-586d-4400-a5e9-32d02007f577

import Definitions.Def_Formalism_PolynomialDimension_StatementHar
import Definitions.Def_Formalism_PolynomialDimension_MultinomialDepth_HarmonicDecompositionHolds
import Definitions.Def_Formalism_PolynomialDimension_MultinomialDepth_DiagLaplacianDivPowMemSqrtFockLattice
import Definitions.Def_Formalism_PolynomialDimension_MultinomialDepth_SqrtFockGaussLatticeComparisonHolds
import Theorems.Thm_Formalism_CountingSumsFrames_Har4_gaussProjText_of
import Theorems.Thm_Formalism_CountingSumsFrames_gaussLatticeProjection_holds

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
theorem _root_.solution : GaussProjText := Har4.gaussProjText_of gaussLatticeProjection_holds
end Formalism.CountingSumsFrames
