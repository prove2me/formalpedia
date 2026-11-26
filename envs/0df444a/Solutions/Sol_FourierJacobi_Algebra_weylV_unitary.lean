-- Prove2me | solution 1 for FourierJacobi.Algebra.weylV_unitary
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T10:18:15.515803+00:00
-- url     : https://prove2.me/submissions/077ad081-944a-4746-9254-14bd966db604

import Definitions.Def_FourierJacobi_Algebra_FiniteCalculation
import Definitions.Def_FourierJacobi_Algebra_UnitaryParameters
import Definitions.Def_FourierJacobi_Algebra_UnitaryFinite

set_option autoImplicit false
open FourierJacobi
open FourierJacobi.Algebra
namespace FourierJacobi.Algebra
theorem _root_.solution {a b : ℂ} (ha : ‖a‖ = 1) (hb : ‖b‖ = 1) (i : Fin 8) :
    ‖weylV a b i‖ = 1 := by
  fin_cases i <;> simp [weylV, ha, hb]
end FourierJacobi.Algebra
