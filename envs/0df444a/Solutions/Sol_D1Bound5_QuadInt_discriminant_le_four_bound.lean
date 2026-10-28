-- Prove2me | solution 1 for D1Bound5.QuadInt.discriminant_le_four_bound
-- status  : ACCEPTED   (prove)
-- author  : @tp
-- created : 2026-10-23T23:21:20.573222+00:00
-- url     : https://prove2.me/submissions/1a6e2caf-28f8-4bee-90a0-6cccdc29267f

import Mathlib.Algebra.QuadraticAlgebra.Basic
import Mathlib.Tactic.Linarith
import Definitions.Def_D1Bound5_Coordinates_Definitions
import Theorems.Thm_D1Bound5_QuadInt_four_norm

section
namespace D1Bound5



namespace QuadInt

variable {tau nu : ℤ}















/-- A nonreal element in a bounded disk bounds the field discriminant.
Used for the Delta<=60 reduction in lem:tail-irregular. -/
theorem _root_.solution (hd : 0 < discriminant tau nu)
    {z : QuadInt tau nu} {M : ℤ} (hM : z.norm ≤ M) (hy : z.im ≠ 0) :
    discriminant tau nu ≤ 4*M := by
  have hypos := sq_pos_of_ne_zero hy
  have hyone : 1 ≤ z.im^2 := by omega
  have hp := mul_le_mul_of_nonneg_left hyone hd.le
  have h := four_norm z
  nlinarith [sq_nonneg (2*z.re+tau*z.im)]

end QuadInt
end D1Bound5
end
