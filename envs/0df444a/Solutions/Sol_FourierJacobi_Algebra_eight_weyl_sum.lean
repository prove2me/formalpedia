-- Prove2me | solution 1 for FourierJacobi.Algebra.eight_weyl_sum
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T13:31:38.753735+00:00
-- url     : https://prove2.me/submissions/6113b30a-22b2-4f60-97d7-f544e6a3bfd9

import Definitions.Def_FourierJacobi_Algebra_WeylSum
import Definitions.Def_FourierJacobi_Algebra_WeylEvaluation
import Theorems.Thm_FourierJacobi_Algebra_weyl_term_cleared
import Theorems.Thm_FourierJacobi_Algebra_weyl_polynomial_identity


set_option autoImplicit false
open FourierJacobi
open FourierJacobi.Algebra
variable {K : Type*} [Field K]
set_option maxHeartbeats 8000000
set_option maxRecDepth 4096
namespace FourierJacobi.Algebra
theorem _root_.solution (t a b d : K) (ha : a ≠ 0) (hb : b ≠ 0) (hd : d ≠ 0)
    (ha₁ : a - 1 ≠ 0) (hb₁ : b - 1 ≠ 0) (hab : a - b ≠ 0) (hab₁ : a * b - 1 ≠ 0)
    (hD : ∀ i, weylKernelDenominator t a b d i ≠ 0)
    (hW : weylCommonDenominator t a b d ≠ 0) :
    (∑ i : Fin 8, weylTerms t a b d i) =
      weylTargetNumerator t a b d / weylCommonDenominator t a b d := by
  apply (eq_div_iff hW).mpr
  rw [mul_comm, Finset.mul_sum]
  simp_rw [weyl_term_cleared t a b d ha hb hd ha₁ hb₁ hab hab₁ _ (hD _)]
  exact weyl_polynomial_identity t a b d
end FourierJacobi.Algebra
