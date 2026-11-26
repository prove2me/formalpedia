-- Prove2me | solution 1 for FourierJacobi.Algebra.satakeNumerator_unitary_ne_zero
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T10:19:26.11542+00:00
-- url     : https://prove2.me/submissions/0b5902b4-a743-4e2e-9ea5-02ad0ff71bea

import Definitions.Def_FourierJacobi_Algebra_FiniteCalculation
import Definitions.Def_FourierJacobi_Algebra_UnitaryParameters
import Definitions.Def_FourierJacobi_Algebra_UnitaryFinite
import Theorems.Thm_FourierJacobi_Algebra_unit_ne_zero


set_option autoImplicit false
open FourierJacobi
open FourierJacobi.Algebra
namespace FourierJacobi.Algebra
theorem _root_.solution {a b : ℂ} (ha : ‖a‖ = 1) (hb : ‖b‖ = 1)
    (hA : 1 + a ≠ 0) (hB : 1 + b ≠ 0) : satakeNumerator a b ≠ 0 :=
  div_ne_zero (mul_ne_zero (pow_ne_zero 2 hA) (pow_ne_zero 2 hB))
    (mul_ne_zero (unit_ne_zero ha) (unit_ne_zero hb))
end FourierJacobi.Algebra
