-- Prove2me | solution 1 for Formalism.CountingSumsFrames.factorial_add_eq_descFactorial_mul
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T13:50:14.594915+00:00
-- url     : https://prove2.me/submissions/9a3885f0-055c-4481-9e2a-8a631ce4587d

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
theorem _root_.solution (a n : ℕ) : (a + n).factorial = (a + n).descFactorial n * a.factorial := by
  have := Nat.factorial_mul_descFactorial (Nat.le_add_left n a)
  rw [Nat.add_sub_cancel] at this
  rw [← this, mul_comm]
end Formalism.CountingSumsFrames
