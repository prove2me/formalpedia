-- Prove2me | solution 1 for D1Bound5.integer_scaled_square_floor_obstruction
-- status  : ACCEPTED   (prove)
-- author  : @tp
-- created : 2026-10-24T03:36:58.918983+00:00
-- url     : https://prove2.me/submissions/3a996e41-b721-49cf-a31e-f3b3555413a4

import Mathlib.Algebra.Order.Ring.Abs
import Mathlib.Algebra.QuadraticAlgebra.Basic
import Mathlib.Data.Int.Sqrt
import Mathlib.Tactic.Linarith
import Theorems.Thm_D1Bound5_integer_square_floor_obstruction

section
namespace D1Bound5



/-- The same obstruction after multiplication by a positive integer.
No divisibility hypothesis or integer division is required. -/
theorem _root_.solution {scale m k : ℤ}
    (hscale : 0 < scale) (hk : 0 ≤ k)
    (hlo : scale * k ^ 2 < m) (hhi : m < scale * (k + 1) ^ 2) :
    ¬ ∃ n : ℤ, m = scale * n ^ 2 := by
  rintro ⟨n, rfl⟩
  exact integer_square_floor_obstruction hk
    ((mul_lt_mul_iff_of_pos_left hscale).mp hlo)
    ((mul_lt_mul_iff_of_pos_left hscale).mp hhi) ⟨n, rfl⟩







namespace QuadInt









end QuadInt
end D1Bound5
end
