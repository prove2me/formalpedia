-- Prove2me | solution 1 for D1Bound5.negative_integer_square_dvd_trace_one
-- status  : ACCEPTED   (prove)
-- author  : @tp
-- created : 2026-10-24T03:36:54.969461+00:00
-- url     : https://prove2.me/submissions/33786151-1c94-4d8f-8517-72359d7b16d5

import Mathlib.Algebra.QuadraticAlgebra.Basic
import Mathlib.Data.Int.Sqrt
import Mathlib.Tactic.Linarith
import Definitions.Def_D1Bound5_Coordinates_Definitions
import Definitions.Def_D1Bound5_RationalSquares_Definitions
import Theorems.Thm_D1Bound5_quadInt_eq_intCast_of_im_eq_zero

section
namespace D1Bound5





/-- In the trace-one model, a negative rational integer square has
real coordinate divisible by 4*nu-1. No positivity assumption on this
parameter is required for the necessary divisibility condition. -/
theorem _root_.solution {nu : ℤ}
    (z : QuadInt 1 nu) (him : z.im = 0) (hre : z.re < 0)
    (hsquare : ∃ r : QuadInt 1 nu, r * r = z) : (4 * nu - 1) ∣ z.re := by
  obtain ⟨r, hr⟩ := hsquare
  have hcast : r * r = (z.re : QuadInt 1 nu) :=
    hr.trans (quadInt_eq_intCast_of_im_eq_zero z him)
  obtain ⟨y, hy⟩ := negative_integer_square_trace_one hre ⟨r, hcast⟩
  refine ⟨-(y ^ 2), ?_⟩
  rw [hy]
  ring





end D1Bound5
end
