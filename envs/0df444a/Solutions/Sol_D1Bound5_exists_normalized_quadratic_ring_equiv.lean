-- Prove2me | solution 1 for D1Bound5.exists_normalized_quadratic_ring_equiv
-- status  : ACCEPTED   (prove)
-- author  : @tp
-- created : 2026-10-23T23:06:46.829827+00:00
-- url     : https://prove2.me/submissions/b651f13f-67d6-4cd4-8241-569b56c53260

import Mathlib.Algebra.QuadraticAlgebra.Basic
import Mathlib.Data.Int.GCD
import Mathlib.LinearAlgebra.Dimension.Free
import Mathlib.NumberTheory.NumberField.Norm
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.LinearCombination
import Definitions.Def_D1Bound5_CoordinateChange_Definitions
import Definitions.Def_D1Bound5_Coordinates_Definitions
import Theorems.Thm_D1Bound5_exists_quadratic_ring_equiv

section
open scoped NumberField
open Module

namespace D1Bound5

variable {K : Type*} [Field K] [NumberField K]








/-- Every quadratic number ring has normalized integral coordinates with
trace zero or one. No maximal-order or discriminant condition is assumed. -/
theorem _root_.solution (hK : finrank ℚ K = 2) :
    ∃ tau nu : ℤ, (tau = 0 ∨ tau = 1) ∧ Nonempty (QuadInt tau nu ≃+* 𝓞 K) := by
  obtain ⟨tau, nu, ⟨e⟩⟩ := exists_quadratic_ring_equiv hK
  refine ⟨tau-2*(tau/2), nu-tau*(tau/2)+(tau/2)^2, ?_,
    ⟨(QuadInt.shift tau nu (tau/2)).trans e⟩⟩
  omega

end D1Bound5
end
