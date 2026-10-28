-- Prove2me | solution 1 for D1Bound5.negative_integer_square_dvd_trace_zero
-- status  : ACCEPTED   (prove)
-- author  : @tp
-- created : 2026-10-24T03:36:55.777766+00:00
-- url     : https://prove2.me/submissions/2c986ceb-f366-4f25-863f-31502b37be9c

import Mathlib.Algebra.QuadraticAlgebra.Basic
import Mathlib.Data.Int.Sqrt
import Mathlib.Tactic.Linarith
import Definitions.Def_D1Bound5_Coordinates_Definitions
import Definitions.Def_D1Bound5_RationalSquares_Definitions
import Theorems.Thm_D1Bound5_quadInt_eq_intCast_of_im_eq_zero

section
namespace D1Bound5



/-- In the trace-zero model, a negative rational integer square has
real coordinate divisible by nu. The existing coordinate classification
includes all possible roots, including zero-coordinate cases. -/
theorem _root_.solution {nu : ℤ}
    (z : QuadInt 0 nu) (him : z.im = 0) (hre : z.re < 0)
    (hsquare : ∃ r : QuadInt 0 nu, r * r = z) : nu ∣ z.re := by
  obtain ⟨r, hr⟩ := hsquare
  have hcast : r * r = (z.re : QuadInt 0 nu) :=
    hr.trans (quadInt_eq_intCast_of_im_eq_zero z him)
  obtain ⟨y, hy⟩ := negative_integer_square_trace_zero hre ⟨r, hcast⟩
  refine ⟨-(y ^ 2), ?_⟩
  rw [hy]
  ring







end D1Bound5
end
