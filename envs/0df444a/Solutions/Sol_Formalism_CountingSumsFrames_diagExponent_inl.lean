-- Prove2me | solution 1 for Formalism.CountingSumsFrames.diagExponent_inl
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-22T23:41:31.507803+00:00
-- url     : https://prove2.me/submissions/b805cac5-e07c-4179-8a37-bcd355f70e91

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
theorem _root_.solution (i j : Fin k) (n : ℕ) : h3s i n (Sum.inl j) = if i = j then n else 0 := by
  simp [h3s, Finsupp.single_apply]
end Formalism.CountingSumsFrames
