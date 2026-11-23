-- Prove2me | solution 1 for Formalism.CountingSumsFrames.diagMul_commute
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T13:46:47.620117+00:00
-- url     : https://prove2.me/submissions/23d44a84-9c9c-4102-802d-c71a41903d84

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
theorem _root_.solution (i j : Fin k) : Commute (h3e K i) (h3e K j) := by
  refine LinearMap.ext fun f => ?_
  simp only [Module.End.mul_apply, h3e, LinearMap.mulLeft_apply]
  ring
end Formalism.CountingSumsFrames
