-- Prove2me | solution 1 for FourierJacobi.Algebra.eight_weyl_sum_closed
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T13:32:16.658772+00:00
-- url     : https://prove2.me/submissions/3c8db122-9e7a-494a-822b-e16e15b726ed

import Definitions.Def_FourierJacobi_Algebra_WeylSum
import Definitions.Def_FourierJacobi_Algebra_WeylEvaluation
import Theorems.Thm_FourierJacobi_Algebra_eight_weyl_sum
import Theorems.Thm_FourierJacobi_Algebra_weyl_common_euler_factorization
import Theorems.Thm_FourierJacobi_Algebra_weyl_target_cleared

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
    (∑ i : Fin 8, weylTerms t a b d i) = weylClosedExpression t a b d := by
  have he := hW
  rw [weyl_common_euler_factorization t a b d ha hb hd] at he
  have he' := (mul_ne_zero_iff.mp he).2
  rw [eight_weyl_sum t a b d ha hb hd ha₁ hb₁ hab hab₁ hD hW]
  exact ((eq_div_iff hW).mpr (by
    simpa [mul_comm] using weyl_target_cleared t a b d ha hb hd he')).symm
end FourierJacobi.Algebra
