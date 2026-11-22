-- Prove2me | solution 1 for Formalism.CountingSumsFrames.descFactorial_cast_eq
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-22T23:41:31.641746+00:00
-- url     : https://prove2.me/submissions/da8e988e-2256-4eba-b342-0fd28d7ead0f

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
theorem _root_.solution (a n : ℕ) :
    (((a + n).descFactorial n : ℕ) : K) = (n.factorial : K) * (((a + n).choose n : ℕ) : K) := by
  rw [Nat.descFactorial_eq_factorial_mul_choose]; push_cast; ring
end Formalism.CountingSumsFrames
