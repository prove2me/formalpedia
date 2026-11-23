-- Prove2me | solution 1 for Formalism.CountingSumsFrames.diagExponent_inr
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T13:44:20.688583+00:00
-- url     : https://prove2.me/submissions/0524c7ba-0fdc-4e00-ac6e-912ef6776f90

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
theorem _root_.solution (i j : Fin k) (n : ℕ) : h3s i n (Sum.inr j) = if i = j then n else 0 := by
  simp [h3s, Finsupp.single_apply]
end Formalism.CountingSumsFrames
