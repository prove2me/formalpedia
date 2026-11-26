-- Prove2me | solution 1 for FourierJacobi.Algebra.weyl_denominator_factorization
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T11:18:58.267036+00:00
-- url     : https://prove2.me/submissions/f380a168-9fda-421f-a798-79b126a6827c

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
    (ha : a ≠ 0) (hb : b ≠ 0) (hd : d ≠ 0) (i : Fin 8) :
    weylCommonDenominator t a b d =
      weylWall a b * weylKernelDenominator t a b d i *
        (a ^ 2 * b ^ 2 * weylScale a b i) * weylRemainingFactors t a b d i := by
  fin_cases i <;>
    simp [weylCommonDenominator, weylKernelDenominator, weylV,
      weylScale, weylRemainingFactors] <;> field_simp <;> ring
end FourierJacobi.Algebra
