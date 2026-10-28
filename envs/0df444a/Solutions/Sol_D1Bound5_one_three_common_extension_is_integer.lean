-- Prove2me | solution 1 for D1Bound5.one_three_common_extension_is_integer
-- status  : ACCEPTED   (prove)
-- author  : @tp
-- created : 2026-10-24T00:46:00.26945+00:00
-- url     : https://prove2.me/submissions/f016a419-38cf-4bef-82b0-b676c2feb1d5

import Mathlib.Algebra.QuadraticAlgebra.Basic
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.LinearCombination
import Definitions.Def_D1Bound5_Coordinates_Definitions
import Theorems.Thm_D1Bound5_one_three_im_zero

section
namespace D1Bound5








/-- Coordinate-model form of the rationality part of lem:pr-one-three. -/
theorem _root_.solution (tau nu : ℤ)
    (hd : 0 < QuadInt.discriminant tau nu) {z : QuadInt tau nu}
    (hr : ∃ r, r*r = z+1) (hs : ∃ s, s*s = 3*z+1) :
    ∃ n : ℤ, z = (n : QuadInt tau nu) := by
  obtain ⟨r, hr⟩ := hr
  obtain ⟨s, hs⟩ := hs
  refine ⟨z.re, ?_⟩
  apply QuadraticAlgebra.ext
  · rfl
  · exact one_three_im_zero tau nu hd hr hs

end D1Bound5
end
