-- Prove2me | solution 1 for D1Bound5.coordinateSquareSieveValid_cons
-- status  : ACCEPTED   (prove)
-- author  : @tp
-- created : 2026-10-24T05:02:59.14637+00:00
-- url     : https://prove2.me/submissions/685e6f31-4bdf-4bae-8ebc-c42f7d053fa3

import Mathlib.Algebra.QuadraticAlgebra.Basic
import Mathlib.Data.Int.Sqrt
import Mathlib.Data.ZMod.Basic
import Mathlib.Tactic.Linarith
import Definitions.Def_D1Bound5_FastSquareTest_Definitions

section
namespace D1Bound5







end D1Bound5

namespace D1Bound5



theorem _root_.solution {tau nu : ℤ} {k mask : ℕ}
    {tail : List (ℕ × ℕ)}
    (hm : CoordinateSquareMaskValid tau nu k mask)
    (ht : CoordinateSquareSieveValid tau nu tail) :
    CoordinateSquareSieveValid tau nu ((k,mask)::tail) := by
  intro item hi
  rcases List.mem_cons.mp hi with he | htail
  · subst item
    exact hm
  · exact ht item htail

end D1Bound5
end
