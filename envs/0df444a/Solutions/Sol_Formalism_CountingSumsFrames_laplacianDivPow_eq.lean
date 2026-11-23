-- Prove2me | solution 1 for Formalism.CountingSumsFrames.laplacianDivPow_eq
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T13:51:53.809574+00:00
-- url     : https://prove2.me/submissions/e4218c43-66fa-4f57-a4d5-ec99f1e00653

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
theorem _root_.solution (l : ℕ) : ctrDiv K k l = ((l.factorial : K)⁻¹) • (∑ i : Fin k, h3d K i) ^ l := rfl
end Formalism.CountingSumsFrames
