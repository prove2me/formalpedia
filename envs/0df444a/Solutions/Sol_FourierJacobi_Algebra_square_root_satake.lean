-- Prove2me | solution 1 for FourierJacobi.Algebra.square_root_satake
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T11:19:46.550826+00:00
-- url     : https://prove2.me/submissions/98608fae-f5ee-4e38-8dfd-baff0e305cc8

import Definitions.Def_FourierJacobi_Algebra_FiniteCalculation
import Definitions.Def_FourierJacobi_Algebra_UnitaryParameters
import Definitions.Def_FourierJacobi_Algebra_UnitaryFinite

set_option autoImplicit false
open FourierJacobi
open FourierJacobi.Algebra
namespace FourierJacobi.Algebra
theorem _root_.solution {K : Type*} [Field K] (a z : K)
    (ha : a ≠ 0) (hz : z ^ 2 = a) :
    (z⁻¹ + z) ^ 2 = a + 2 + a⁻¹ := by
  have hz₀ : z ≠ 0 := by
    intro he
    apply ha
    rw [← hz, he]
    simp
  rw [← hz]
  field_simp
  ring
end FourierJacobi.Algebra
