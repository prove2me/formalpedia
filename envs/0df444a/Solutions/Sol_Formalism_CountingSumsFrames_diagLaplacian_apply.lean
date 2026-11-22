-- Prove2me | solution 1 for Formalism.CountingSumsFrames.diagLaplacian_apply
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-22T23:41:36.885463+00:00
-- url     : https://prove2.me/submissions/ada8dc3e-cc03-4287-b41a-d6c237d73cdb

import Definitions.Def_Formalism_PolynomialDimension_StatementHar
import Definitions.Def_Formalism_PolynomialDimension_MultinomialDepth_DiagLaplacianDivPowMemSqrtFockLattice

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
variable {K : Type} [Field K] [CharZero K] {k : ℕ}
namespace Formalism.CountingSumsFrames
theorem _root_.solution (i : Fin k) (f : PolXY K k) :
    h3d K i f = pderiv (Sum.inl i) (pderiv (Sum.inr i) f) := rfl
end Formalism.CountingSumsFrames
