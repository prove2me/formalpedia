-- Prove2me | solution 1 for Formalism.CountingSumsFrames.diagMul_pow_apply
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T13:50:13.335947+00:00
-- url     : https://prove2.me/submissions/0bc7f0a0-7c6c-458e-be5c-716a198a742a

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
theorem _root_.solution (i : Fin k) (n : ℕ) (f : PolXY K k) :
    (h3e K i ^ n) f = monomial (h3s i n) (1 : K) * f := by
  have : (monomial (h3s i n) (1 : K) : PolXY K k) = (X (Sum.inl i) * X (Sum.inr i)) ^ n := by
    rw [mul_pow, X_pow_eq_monomial, X_pow_eq_monomial, monomial_mul, one_mul, h3s]
  rw [this, h3e, LinearMap.pow_mulLeft, LinearMap.mulLeft_apply]
end Formalism.CountingSumsFrames
