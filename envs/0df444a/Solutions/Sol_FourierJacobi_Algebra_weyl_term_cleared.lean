-- Prove2me | solution 1 for FourierJacobi.Algebra.weyl_term_cleared
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T11:23:02.598021+00:00
-- url     : https://prove2.me/submissions/307f80a2-734b-4017-b06a-1be0c17c1c82

import Definitions.Def_FourierJacobi_Algebra_WeylSum
import Definitions.Def_FourierJacobi_Algebra_WeylEvaluation
import Theorems.Thm_FourierJacobi_Algebra_weyl_weights_cleared
import Theorems.Thm_FourierJacobi_Algebra_weyl_height_cleared
import Theorems.Thm_FourierJacobi_Algebra_weyl_denominator_factorization
section
namespace FourierJacobi
namespace Algebra
variable {K : Type*} [Field K]
set_option maxHeartbeats 8000000
set_option maxRecDepth 4096
private theorem clear_weighted_kernel (R A An S H Hn D B : K) (hD : D ≠ 0)
    (hA : R * A = An) (hH : S * H = Hn) :
    (R * D * S * B) * (A * (H / D)) = An * Hn * B := by
  calc
    _ = (R * A) * (S * H) * B := by field_simp
    _ = _ := by rw [hA, hH]
end Algebra
end FourierJacobi
end

set_option autoImplicit false
open FourierJacobi
open FourierJacobi.Algebra
variable {K : Type*} [Field K]
set_option maxHeartbeats 8000000
set_option maxRecDepth 4096
namespace FourierJacobi.Algebra
theorem _root_.solution (t a b d : K) (ha : a ≠ 0) (hb : b ≠ 0) (hd : d ≠ 0)
    (ha₁ : a - 1 ≠ 0) (hb₁ : b - 1 ≠ 0) (hab : a - b ≠ 0) (hab₁ : a * b - 1 ≠ 0)
    (i : Fin 8) (hD : weylKernelDenominator t a b d i ≠ 0) :
    weylCommonDenominator t a b d * weylTerms t a b d i =
      weylClearedTerms t a b d i := by
  rw [weyl_denominator_factorization t a b d ha hb hd i]
  exact clear_weighted_kernel _ _ _ _ _ _ _ _ hD
    (weyl_weights_cleared t a b ha hb ha₁ hb₁ hab hab₁ i)
    (weyl_height_cleared t a b d ha hb i)
end FourierJacobi.Algebra
