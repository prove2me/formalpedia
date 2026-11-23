-- Prove2me | solution 1 for Formalism.CountingSumsFrames.Har4.xDeg_single_inr
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T10:42:46.501456+00:00
-- url     : https://prove2.me/submissions/39b88347-8bc2-40e3-8846-2be34503263c

import Definitions.Def_Formalism_PolynomialDimension_StatementHar
import Definitions.Def_Formalism_PolynomialDimension_MultinomialDepth_HarmonicDecompositionHolds
import Definitions.Def_Formalism_PolynomialDimension_MultinomialDepth_DiagLaplacianDivPowMemSqrtFockLattice
import Definitions.Def_Formalism_PolynomialDimension_MultinomialDepth_SqrtFockGaussLatticeComparisonHolds

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
open Formalism.CountingSumsFrames.Har4
namespace Formalism.CountingSumsFrames.Har4
theorem _root_.solution {k : ℕ} (i : Fin k) (n : ℕ) : xDeg (Finsupp.single (Sum.inr i : XY k) n) = 0 := by
  simp [xDeg, Finsupp.single_apply]
end Formalism.CountingSumsFrames.Har4
