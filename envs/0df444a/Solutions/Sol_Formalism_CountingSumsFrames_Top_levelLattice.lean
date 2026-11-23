-- Prove2me | solution 1 for Formalism.CountingSumsFrames.Top.levelLattice
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T13:54:10.530347+00:00
-- url     : https://prove2.me/submissions/7a18e479-66a5-477e-99b9-ab1355456c1c

import Definitions.Def_Formalism_PolynomialDimension_MultinomialDepth_PairingAdjointLaplacianHolds
import Definitions.Def_Formalism_PolynomialDimension_MultinomialDepth_HarmonicDecompositionHolds
import Definitions.Def_Formalism_PolynomialDimension_MultinomialDepth_DiagLaplacianDivPowMemSqrtFockLattice
import Definitions.Def_Formalism_PolynomialDimension_MultinomialDepth_SqrtFockGaussLatticeComparisonHolds
import Definitions.Def_Formalism_PolynomialDimension_FinalHar
import Theorems.Thm_Formalism_CountingSumsFrames_Har4_isotypicLattice_holds
import Theorems.Thm_Formalism_CountingSumsFrames_isotypicLattice_holds


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
theorem _root_.solution : Formalism.CountingSumsFrames.LevelLattice := Formalism.CountingSumsFrames.isotypicLattice_holds
end Formalism.CountingSumsFrames.Top
