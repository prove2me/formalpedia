-- Prove2me | solution 1 for FourierJacobi.Algebra.weylV_one_add_ne_zero
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T13:29:50.225952+00:00
-- url     : https://prove2.me/submissions/e2b77b3b-b36c-438b-a734-a92435032ed3

import Definitions.Def_FourierJacobi_Algebra_FiniteCalculation
import Definitions.Def_FourierJacobi_Algebra_UnitaryParameters
import Definitions.Def_FourierJacobi_Algebra_UnitaryFinite
import Theorems.Thm_FourierJacobi_Algebra_one_add_inv_ne_zero

set_option autoImplicit false
open FourierJacobi
open FourierJacobi.Algebra
namespace FourierJacobi.Algebra
theorem _root_.solution {a b : ℂ} (ha : a ≠ 0) (hb : b ≠ 0)
    (hA : 1 + a ≠ 0) (hB : 1 + b ≠ 0) (i : Fin 8) :
    1 + weylV a b i ≠ 0 := by
  have hAi := one_add_inv_ne_zero ha hA
  have hBi := one_add_inv_ne_zero hb hB
  fin_cases i
  · simpa [weylV] using hA
  · simpa [weylV] using hB
  · simpa [weylV] using hA
  · simpa [weylV] using hBi
  · simpa [weylV] using hB
  · simpa [weylV] using hAi
  · simpa [weylV] using hBi
  · simpa [weylV] using hAi
end FourierJacobi.Algebra
