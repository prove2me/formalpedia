-- Prove2me | solution 1 for FourierJacobi.Algebra.weyl_target_cleared
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T11:20:41.215612+00:00
-- url     : https://prove2.me/submissions/fc210d28-36df-4101-ae25-84ad70babd52

import Definitions.Def_FourierJacobi_Algebra_WeylSum
import Definitions.Def_FourierJacobi_Algebra_WeylEvaluation
import Theorems.Thm_FourierJacobi_Algebra_weyl_common_euler_factorization
import Theorems.Thm_FourierJacobi_Algebra_weyl_target_numerator_eq

set_option autoImplicit false
open FourierJacobi
open FourierJacobi.Algebra
variable {K : Type*} [Field K]
set_option maxHeartbeats 8000000
set_option maxRecDepth 4096
namespace FourierJacobi.Algebra
theorem _root_.solution (t a b d : K)
    (ha : a ≠ 0) (hb : b ≠ 0) (hd : d ≠ 0)
    (hD : d₁ t a b d * d₂ t a b d ≠ 0) :
    weylCommonDenominator t a b d * weylClosedExpression t a b d =
      weylTargetNumerator t a b d := by
  rw [weyl_common_euler_factorization t a b d ha hb hd, weyl_target_numerator_eq t a b d ha hb]
  unfold weylClosedExpression
  generalize (d₁ t a b d * d₂ t a b d) = D at *
  field_simp
end FourierJacobi.Algebra
