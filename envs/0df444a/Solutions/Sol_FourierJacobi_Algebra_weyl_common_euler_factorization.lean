-- Prove2me | solution 1 for FourierJacobi.Algebra.weyl_common_euler_factorization
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T11:19:48.30298+00:00
-- url     : https://prove2.me/submissions/96333cf7-3ea4-4883-af84-e1bd18d8525e

import Definitions.Def_FourierJacobi_Algebra_WeylSum
import Definitions.Def_FourierJacobi_Algebra_WeylEvaluation
import Theorems.Thm_FourierJacobi_Algebra_tensor_denominator_cleared

set_option autoImplicit false
open FourierJacobi
open FourierJacobi.Algebra
variable {K : Type*} [Field K]
set_option maxHeartbeats 8000000
set_option maxRecDepth 4096
namespace FourierJacobi.Algebra
theorem _root_.solution (t a b d : K)
    (ha : a ≠ 0) (hb : b ≠ 0) (hd : d ≠ 0) :
    weylCommonDenominator t a b d =
      (weylWall a b * a ^ 2 * b ^ 2 * d * (a ^ 2 * b ^ 2 * d ^ 4)) *
        (d₁ t a b d * d₂ t a b d) := by
  calc
    _ = (weylWall a b * a ^ 2 * b ^ 2 * d) *
        tensorDenominatorPolynomial t a b d := by
      unfold weylCommonDenominator tensorDenominatorPolynomial
      ring
    _ = _ := by rw [← tensor_denominator_cleared t a b d ha hb hd]; ring
end FourierJacobi.Algebra
