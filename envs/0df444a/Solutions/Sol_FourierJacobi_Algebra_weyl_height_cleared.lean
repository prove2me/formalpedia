-- Prove2me | solution 1 for FourierJacobi.Algebra.weyl_height_cleared
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T11:18:57.664525+00:00
-- url     : https://prove2.me/submissions/602b1053-bb3b-4b63-aabf-2db424f017b7

import Definitions.Def_FourierJacobi_Algebra_WeylSum
import Definitions.Def_FourierJacobi_Algebra_WeylEvaluation

set_option autoImplicit false
open FourierJacobi
open FourierJacobi.Algebra
variable {K : Type*} [Field K]
set_option maxHeartbeats 8000000
set_option maxRecDepth 4096
namespace FourierJacobi.Algebra
theorem _root_.solution (t a b d : K) (ha : a ≠ 0) (hb : b ≠ 0) (i : Fin 8) :
    (a ^ 2 * b ^ 2 * weylScale a b i) *
      kernelNumerator t d (weylU a b i) (weylV a b i) =
      weylHeightNumerators t a b d i := by
  fin_cases i <;>
    simp [weylScale, weylU, weylV, kernelNumerator, weylHeightNumerators,
      weylHeight0, weylHeight1, weylHeight2, weylHeight3,
      weylHeight4, weylHeight5, weylHeight6, weylHeight7] <;>
    field_simp <;> ring
end FourierJacobi.Algebra
