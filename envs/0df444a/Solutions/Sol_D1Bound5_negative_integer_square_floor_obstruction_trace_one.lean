-- Prove2me | solution 1 for D1Bound5.negative_integer_square_floor_obstruction_trace_one
-- status  : ACCEPTED   (prove)
-- author  : @tp
-- created : 2026-10-24T03:36:57.918781+00:00
-- url     : https://prove2.me/submissions/6c31375d-97d1-4255-a8b0-1a3d5a166a50

import Mathlib.Algebra.Order.Ring.Abs
import Mathlib.Algebra.QuadraticAlgebra.Basic
import Mathlib.Data.Int.Sqrt
import Mathlib.Tactic.Linarith
import Definitions.Def_D1Bound5_Coordinates_Definitions
import Definitions.Def_D1Bound5_RationalSquares_Definitions
import Theorems.Thm_D1Bound5_integer_scaled_square_floor_obstruction

section
namespace D1Bound5









/-- Negative rational radicands in the trace-one model reduce to
minus the discriminant times an ordinary integer square. -/
theorem _root_.solution {nu m k : ℤ}
    (hd : 0 < 4 * nu - 1) (hk : 0 ≤ k)
    (hlo : (4 * nu - 1) * k ^ 2 < -m)
    (hhi : -m < (4 * nu - 1) * (k + 1) ^ 2) :
    ¬ ∃ r : QuadInt 1 nu, r * r = (m : QuadInt 1 nu) := by
  intro hr
  have hneg : 0 < -m := lt_of_le_of_lt (mul_nonneg hd.le (sq_nonneg k)) hlo
  have hm : m < 0 := by omega
  obtain ⟨n, hn⟩ := negative_integer_square_trace_one hm hr
  apply integer_scaled_square_floor_obstruction hd hk hlo hhi
  exact ⟨n, by nlinarith only [hn]⟩

namespace QuadInt









end QuadInt
end D1Bound5
end
