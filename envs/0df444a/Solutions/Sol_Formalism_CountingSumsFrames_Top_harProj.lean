-- Prove2me | solution 1 for Formalism.CountingSumsFrames.Top.harProj
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T11:27:01.086809+00:00
-- url     : https://prove2.me/submissions/e699d845-a509-479b-956f-bfd278230c5d

import Definitions.Def_Formalism_PolynomialDimension_MultinomialDepth_PairingAdjointLaplacianHolds
import Definitions.Def_Formalism_PolynomialDimension_MultinomialDepth_HarmonicDecompositionHolds
import Definitions.Def_Formalism_PolynomialDimension_MultinomialDepth_DiagLaplacianDivPowMemSqrtFockLattice
import Definitions.Def_Formalism_PolynomialDimension_MultinomialDepth_SqrtFockGaussLatticeComparisonHolds
import Definitions.Def_Formalism_PolynomialDimension_FinalHar
import Theorems.Thm_Formalism_CountingSumsFrames_harmonicProjection_holds


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
theorem _root_.solution : Formalism.CountingSumsFrames.HarProj := Formalism.CountingSumsFrames.harmonicProjection_holds
end Formalism.CountingSumsFrames.Top
