-- Prove2me | solution 1 for D1Bound5.coordinateSquareMaskBool_of_square
-- status  : ACCEPTED   (prove)
-- author  : @tp
-- created : 2026-10-24T04:18:14.517472+00:00
-- url     : https://prove2.me/submissions/c7847c35-e1cf-42e8-a3bb-646dab914daf

import Mathlib.Algebra.QuadraticAlgebra.Basic
import Mathlib.Data.Int.Sqrt
import Mathlib.Data.ZMod.Basic
import Mathlib.Tactic.Linarith
import Definitions.Def_D1Bound5_Coordinates_Definitions
import Definitions.Def_D1Bound5_FastSquareTest_Definitions

section
namespace D1Bound5
open QuadInt







/-- Reduction of an actual integral square is accepted by a valid finite mask.
No primality, positive discriminant or nonzero-root hypothesis is needed. -/
theorem _root_.solution {tau nu : ℤ}
    (k mask : ℕ) (htable : CoordinateSquareMaskValid tau nu k mask)
    (z r : QuadInt tau nu) (hr : r*r = z) :
    coordinateSquareMaskBool k mask z = true := by
  unfold coordinateSquareMaskBool
  rw [← hr]
  simpa only [QuadraticAlgebra.re_mul, QuadraticAlgebra.im_mul,
    Int.cast_add, Int.cast_mul, Int.cast_neg] using
      htable (r.re : ZMod (k+1)) (r.im : ZMod (k+1))













end D1Bound5
end
