-- Prove2me | solution 1 for Formalism.CountingSumsFrames.coeff_diagMul_pow
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T13:52:28.566843+00:00
-- url     : https://prove2.me/submissions/ece6a4c1-0185-4e9c-b844-cbf55dfb9936

import Definitions.Def_Formalism_PolynomialDimension_StatementHar
import Definitions.Def_Formalism_PolynomialDimension_MultinomialDepth_DiagLaplacianDivPowMemSqrtFockLattice
import Theorems.Thm_Formalism_CountingSumsFrames_diagMul_pow_apply

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
theorem _root_.solution (i : Fin k) (n : ℕ) (f : PolXY K k) (m : XY k →₀ ℕ) :
    coeff m ((h3e K i ^ n) f) = if h3s i n ≤ m then coeff (m - h3s i n) f else 0 := by
  rw [diagMul_pow_apply, coeff_monomial_mul', one_mul]
end Formalism.CountingSumsFrames
