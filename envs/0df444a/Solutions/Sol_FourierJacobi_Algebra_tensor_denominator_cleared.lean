-- Prove2me | solution 1 for FourierJacobi.Algebra.tensor_denominator_cleared
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T11:19:02.485853+00:00
-- url     : https://prove2.me/submissions/5d994af1-a862-46c1-bd9c-2f1963dfc598

import Definitions.Def_FourierJacobi_Algebra_WeylSum
import Definitions.Def_FourierJacobi_Algebra_WeylEvaluation

set_option autoImplicit false
open FourierJacobi
open FourierJacobi.Algebra
variable {K : Type*} [Field K]
set_option maxHeartbeats 8000000
set_option maxRecDepth 4096
namespace FourierJacobi.Algebra
theorem _root_.solution (t a b d : K)
    (ha : a ≠ 0) (hb : b ≠ 0) (hd : d ≠ 0) :
    (a ^ 2 * b ^ 2 * d ^ 4) * (d₁ t a b d * d₂ t a b d) =
      tensorDenominatorPolynomial t a b d := by
  unfold d₁ d₂ fourFactors tensorDenominatorPolynomial
  field_simp
end FourierJacobi.Algebra
