-- Prove2me | solution 1 for D1Bound5.no_three_of_graph_certificate
-- status  : ACCEPTED   (prove)
-- author  : @tp
-- created : 2026-10-24T02:37:47.208569+00:00
-- url     : https://prove2.me/submissions/d109c250-8433-47cd-b7b6-c4e0bbef1245

import Mathlib.Algebra.QuadraticAlgebra.Basic
import Mathlib.Algebra.Ring.Basic
import Mathlib.Algebra.Ring.Equiv
import Mathlib.Analysis.Complex.Basic
import Mathlib.Analysis.Complex.Norm
import Mathlib.Analysis.Complex.Polynomial.Basic
import Mathlib.Data.Finset.Card
import Mathlib.Data.Finset.Prod
import Mathlib.Data.Int.GCD
import Mathlib.Data.Int.Interval
import Mathlib.Data.Int.Sqrt
import Mathlib.Data.ZMod.Basic
import Mathlib.LinearAlgebra.Dimension.Free
import Mathlib.NumberTheory.NumberField.InfinitePlace.TotallyRealComplex
import Mathlib.NumberTheory.NumberField.Norm
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.LinearCombination
import Mathlib.Tactic.Ring
import Definitions.Def_D1Bound5_Coordinates_Definitions
import Definitions.Def_D1Bound5_FastSquareTest_Definitions
import Definitions.Def_D1Bound5_IsD1Tuple
import Definitions.Def_D1Bound5_SmallPairGraphCheck_Definitions
import Theorems.Thm_D1Bound5_hasSquareRootFast_iff

section
open scoped NumberField
open Module

namespace D1Bound5
open QuadInt





/-- The finite graph certificate rules out three compatible vertices with
arbitrary coordinate size. There is no unverified graph computation. -/
theorem _root_.solution {tau nu : ℤ}
    (hd : 0 < discriminant tau nu) (sieve : List (ℕ × ℕ))
    (hvalid : CoordinateSquareSieveValid tau nu sieve) (vertices : List (QuadInt tau nu))
    (hcheck : pairGraphTriangleFreeBool sieve vertices = true)
    (t : Fin 3 → QuadInt tau nu) (ht : IsD1Tuple t)
    (hmem : ∀ i, t i ∈ vertices) : False := by
  have hne (i j : Fin 3) (hij : i ≠ j) : t i ≠ t j := fun h => hij (ht.1 h)
  have hs (i j : Fin 3) (hij : i ≠ j) :
      hasSquareRootFast sieve (t i*t j+1) = true :=
    (hasSquareRootFast_iff hd sieve hvalid _).2 (ht.2.2 i j hij)
  have Ha := List.all_eq_true.mp hcheck (t 0) (hmem 0)
  have ga : decide (t 0 ≠ 0) = true := by simp [ht.2.1 0]
  simp only [ga, if_true] at Ha
  have Hb := List.all_eq_true.mp Ha (t 1) (hmem 1)
  have gb : decide (t 1 ≠ 0 ∧ t 0 ≠ t 1) = true := by
    simp [ht.2.1 1, hne 0 1 (by decide)]
  have hs01 := hs 0 1 (by decide)
  simp only [gb, hs01, if_true] at Hb
  have Hc := List.all_eq_true.mp Hb (t 2) (hmem 2)
  have gc : decide (t 2 ≠ 0 ∧ t 0 ≠ t 2 ∧ t 1 ≠ t 2) = true := by
    simp [ht.2.1 2, hne 0 2 (by decide), hne 1 2 (by decide)]
  have hs02 := hs 0 2 (by decide)
  have hs12 := hs 1 2 (by decide)
  simpa [gc, hs02, hs12] using Hc



end D1Bound5
end
