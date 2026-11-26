-- Prove2me | solution 1 for FourierJacobi.Algebra.one_add_inv_ne_zero
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T11:20:01.061399+00:00
-- url     : https://prove2.me/submissions/fb6e1219-5c21-48e8-981e-601f3501b9ca

import Definitions.Def_FourierJacobi_Algebra_FiniteCalculation
import Definitions.Def_FourierJacobi_Algebra_UnitaryParameters
import Definitions.Def_FourierJacobi_Algebra_UnitaryFinite

set_option autoImplicit false
open FourierJacobi
open FourierJacobi.Algebra
namespace FourierJacobi.Algebra
theorem _root_.solution {z : ℂ} (hz : z ≠ 0) (h : 1 + z ≠ 0) :
    1 + z⁻¹ ≠ 0 := by
  intro he
  have he' := congrArg (fun x : ℂ => x * z) he
  apply h
  simpa [add_mul, hz, add_comm] using he'
end FourierJacobi.Algebra
