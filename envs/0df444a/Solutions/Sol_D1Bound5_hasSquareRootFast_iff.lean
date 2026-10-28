-- Prove2me | solution 1 for D1Bound5.hasSquareRootFast_iff
-- status  : ACCEPTED   (prove)
-- author  : @tp
-- created : 2026-10-24T02:37:58.272775+00:00
-- url     : https://prove2.me/submissions/a47bed42-8ffd-4b0f-a360-3f8c577d1a95

import Mathlib.Algebra.QuadraticAlgebra.Basic
import Mathlib.Data.Int.Sqrt
import Mathlib.Data.ZMod.Basic
import Mathlib.Tactic.Linarith
import Definitions.Def_D1Bound5_Coordinates_Definitions
import Definitions.Def_D1Bound5_FastSquareTest_Definitions
import Definitions.Def_D1Bound5_SquareTest_Definitions
import Theorems.Thm_D1Bound5_QuadInt_hasSquareRoot_iff
import Theorems.Thm_D1Bound5_coordinateSquareMaskBool_of_square

section
namespace D1Bound5
open QuadInt















theorem coordinateSquareSieveBool_of_square {tau nu : ℤ}
    (sieve : List (ℕ × ℕ)) (hvalid : CoordinateSquareSieveValid tau nu sieve)
    (z : QuadInt tau nu) (hz : ∃ r, r*r = z) :
    coordinateSquareSieveBool sieve z = true := by
  obtain ⟨r, hr⟩ := hz
  apply List.all_eq_true.mpr
  intro item hi
  exact coordinateSquareMaskBool_of_square item.1 item.2 (hvalid item hi) z r hr



theorem _root_.solution {tau nu : ℤ}
    (hd : 0 < discriminant tau nu)
    (sieve : List (ℕ × ℕ)) (hvalid : CoordinateSquareSieveValid tau nu sieve)
    (z : QuadInt tau nu) : hasSquareRootFast sieve z = true ↔ ∃ r, r*r = z := by
  simp only [hasSquareRootFast, Bool.and_eq_true]
  constructor
  · intro h
    exact (hasSquareRoot_iff hd z).1 h.2
  · intro h
    exact ⟨coordinateSquareSieveBool_of_square sieve hvalid z h,
      (hasSquareRoot_iff hd z).2 h⟩

end D1Bound5
end
