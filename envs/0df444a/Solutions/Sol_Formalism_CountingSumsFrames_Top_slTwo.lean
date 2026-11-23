-- Prove2me | solution 1 for Formalism.CountingSumsFrames.Top.slTwo
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T14:06:39.080313+00:00
-- url     : https://prove2.me/submissions/6c365e03-59e1-4d99-825c-a100c05b4856

import Definitions.Def_Formalism_PolynomialDimension_MultinomialDepth_PairingAdjointLaplacianHolds
import Definitions.Def_Formalism_PolynomialDimension_MultinomialDepth_HarmonicDecompositionHolds
import Definitions.Def_Formalism_PolynomialDimension_MultinomialDepth_DiagLaplacianDivPowMemSqrtFockLattice
import Definitions.Def_Formalism_PolynomialDimension_MultinomialDepth_SqrtFockGaussLatticeComparisonHolds
import Definitions.Def_Formalism_PolynomialDimension_FinalHar
import Theorems.Thm_Formalism_CountingSumsFrames_slTwoCommutator_holds


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
theorem _root_.solution : Formalism.CountingSumsFrames.SlTwo := Formalism.CountingSumsFrames.slTwoCommutator_holds
end Formalism.CountingSumsFrames.Top
