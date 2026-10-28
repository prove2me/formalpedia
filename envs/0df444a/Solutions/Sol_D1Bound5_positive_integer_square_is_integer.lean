-- Prove2me | solution 1 for D1Bound5.positive_integer_square_is_integer
-- status  : ACCEPTED   (prove)
-- author  : @tp
-- created : 2026-10-24T05:00:31.940979+00:00
-- url     : https://prove2.me/submissions/8fd092d5-c395-4c10-9873-b9a11d14dbfd

import Mathlib.Algebra.QuadraticAlgebra.Basic
import Mathlib.Data.Int.Sqrt
import Mathlib.Tactic.Linarith
import Definitions.Def_D1Bound5_Coordinates_Definitions
import Definitions.Def_D1Bound5_RationalSquares_Definitions

section
namespace D1Bound5

open QuadInt









/-- A positive rational integer that is a square in an imaginary quadratic
integer ring is already an ordinary integer square. -/
theorem _root_.solution {tau nu m : ℤ}
    (hd : 0 < discriminant tau nu) (hm : 0 < m)
    (hr : ∃ r : QuadInt tau nu, r*r = (m : QuadInt tau nu)) :
    ∃ n : ℤ, m = n^2 := by
  obtain ⟨r,hr⟩ := hr
  rcases rational_integer_square_cases r hr with ⟨_, h⟩ | ⟨_, h⟩
  · exact ⟨r.re, by nlinarith only [h]⟩
  · have hp := mul_nonneg hd.le (sq_nonneg r.im)
    exfalso
    nlinarith only [hm, hp, h]

end D1Bound5
end
