-- Prove2me | solution 1 for D1Bound5.integer_square_floor_obstruction
-- status  : ACCEPTED   (prove)
-- author  : @tp
-- created : 2026-10-24T04:42:07.435452+00:00
-- url     : https://prove2.me/submissions/597aef60-9d8e-4ced-80d0-b77eaa6f3833

import Mathlib.Algebra.Order.Ring.Abs
import Mathlib.Algebra.QuadraticAlgebra.Basic
import Mathlib.Data.Int.Sqrt
import Mathlib.Tactic.Linarith

section
namespace D1Bound5

/-- An integer strictly between consecutive nonnegative integer squares
cannot itself be a square. The witness is checked by integer arithmetic. -/
theorem _root_.solution {m k : ℤ}
    (hk : 0 ≤ k) (hlo : k ^ 2 < m) (hhi : m < (k + 1) ^ 2) :
    ¬ ∃ n : ℤ, m = n ^ 2 := by
  rintro ⟨n, rfl⟩
  have hlo' : k ^ 2 < |n| ^ 2 := by simpa only [sq_abs] using hlo
  have hhi' : |n| ^ 2 < (k + 1) ^ 2 := by simpa only [sq_abs] using hhi
  have hnlo : k < |n| := (sq_lt_sq₀ hk (abs_nonneg n)).mp hlo'
  have hnhi : |n| < k + 1 := (sq_lt_sq₀ (abs_nonneg n) (by omega)).mp hhi'
  omega









namespace QuadInt









end QuadInt
end D1Bound5
end
