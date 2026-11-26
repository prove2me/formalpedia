-- Prove2me | solution 1 for FourierJacobi.Algebra.principalAdjointInverse_eq
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T09:41:28.352817+00:00
-- url     : https://prove2.me/submissions/0dd919ab-4402-4695-a2b2-933bccd0e5e1

import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Ring
import Definitions.Def_FourierJacobi_Algebra_EulerFactors

set_option autoImplicit false
open FourierJacobi
open FourierJacobi.Algebra
variable {K : Type*} [Field K]
namespace FourierJacobi.Algebra
theorem _root_.solution (t d : K) :
    principalAdjointInverse t d =
      (1 - d ^ 2 * t ^ 2) * (1 - t ^ 2) * (1 - t ^ 2 / d ^ 2) := by
  unfold principalAdjointInverse
  simp only [div_eq_mul_inv]
  ring
end FourierJacobi.Algebra
