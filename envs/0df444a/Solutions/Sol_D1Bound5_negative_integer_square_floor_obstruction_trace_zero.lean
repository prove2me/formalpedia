-- Prove2me | solution 1 for D1Bound5.negative_integer_square_floor_obstruction_trace_zero
-- status  : ACCEPTED   (prove)
-- author  : @tp
-- created : 2026-10-24T03:36:56.761563+00:00
-- url     : https://prove2.me/submissions/3f16a477-91c9-40c8-88a9-c3cfb1ed16b0

import Mathlib.Algebra.Order.Ring.Abs
import Mathlib.Algebra.QuadraticAlgebra.Basic
import Mathlib.Data.Int.Sqrt
import Mathlib.Tactic.Linarith
import Definitions.Def_D1Bound5_Coordinates_Definitions
import Definitions.Def_D1Bound5_RationalSquares_Definitions
import Theorems.Thm_D1Bound5_integer_scaled_square_floor_obstruction

section
namespace D1Bound5







/-- Negative rational radicands in the trace-zero model reduce to
minus the defining parameter times an ordinary integer square. -/
theorem _root_.solution {nu m k : ℤ}
    (hnu : 0 < nu) (hk : 0 ≤ k)
    (hlo : nu * k ^ 2 < -m) (hhi : -m < nu * (k + 1) ^ 2) :
    ¬ ∃ r : QuadInt 0 nu, r * r = (m : QuadInt 0 nu) := by
  intro hr
  have hneg : 0 < -m := lt_of_le_of_lt (mul_nonneg hnu.le (sq_nonneg k)) hlo
  have hm : m < 0 := by omega
  obtain ⟨n, hn⟩ := negative_integer_square_trace_zero hm hr
  apply integer_scaled_square_floor_obstruction hnu hk hlo hhi
  exact ⟨n, by nlinarith only [hn]⟩



namespace QuadInt









end QuadInt
end D1Bound5
end
