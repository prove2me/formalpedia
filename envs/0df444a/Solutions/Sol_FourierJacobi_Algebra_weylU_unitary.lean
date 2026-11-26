-- Prove2me | solution 1 for FourierJacobi.Algebra.weylU_unitary
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T10:17:56.053293+00:00
-- url     : https://prove2.me/submissions/b1afe12f-578a-427e-a675-e6c9b4f41484

import Definitions.Def_FourierJacobi_Algebra_FiniteCalculation
import Definitions.Def_FourierJacobi_Algebra_UnitaryParameters
import Definitions.Def_FourierJacobi_Algebra_UnitaryFinite

set_option autoImplicit false
open FourierJacobi
open FourierJacobi.Algebra
namespace FourierJacobi.Algebra
theorem _root_.solution {a b : ℂ} (ha : ‖a‖ = 1) (hb : ‖b‖ = 1) (i : Fin 8) :
    ‖weylU a b i‖ = 1 := by
  fin_cases i <;> simp [weylU, ha, hb]
end FourierJacobi.Algebra
