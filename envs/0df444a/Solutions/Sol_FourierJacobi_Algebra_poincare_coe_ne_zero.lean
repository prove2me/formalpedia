-- Prove2me | solution 1 for FourierJacobi.Algebra.poincare_coe_ne_zero
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T10:18:57.386404+00:00
-- url     : https://prove2.me/submissions/e8aae0c4-e7bf-4e4d-887e-93dccccf8e55

import Definitions.Def_FourierJacobi_Algebra_FiniteCalculation
import Definitions.Def_FourierJacobi_Algebra_UnitaryParameters
import Definitions.Def_FourierJacobi_Algebra_UnitaryFinite

set_option autoImplicit false
open FourierJacobi
open FourierJacobi.Algebra
namespace FourierJacobi.Algebra
theorem _root_.solution (t : ℝ) : poincare (t : ℂ) ≠ 0 := by
  have hp : 0 < poincare t := by unfold poincare; positivity
  have hc : poincare (t : ℂ) = ((poincare t : ℝ) : ℂ) := by
    simp [poincare]
  rw [hc]
  exact_mod_cast ne_of_gt hp
end FourierJacobi.Algebra
