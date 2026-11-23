-- Prove2me | solution 1 for Formalism.CountingSumsFrames.Har4.xFact_ne_zero
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T10:42:57.726267+00:00
-- url     : https://prove2.me/submissions/0243be21-f8af-43a3-8922-205e5744ae3d

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
theorem _root_.solution {k : ℕ} (m : XY k →₀ ℕ) : xFact m ≠ 0 :=
  Finset.prod_ne_zero_iff.2 (fun i _ => Nat.factorial_ne_zero _)
end Formalism.CountingSumsFrames.Har4
