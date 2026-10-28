-- Prove2me | solution 1 for D1Bound5.pairCachedCoordinateSieveBool_signatures
-- status  : ACCEPTED   (prove)
-- author  : @tp
-- created : 2026-10-24T03:36:10.754361+00:00
-- url     : https://prove2.me/submissions/c33dba24-d373-4078-96eb-ddacd35d1b60

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
import Definitions.Def_D1Bound5_PairCachedResidues_Definitions
import Theorems.Thm_D1Bound5_pairResidueMaskBool_coordinates

section
namespace D1Bound5











theorem _root_.solution {tau nu : ℤ}
    (sieve : List (ℕ × ℕ)) (x y : QuadInt tau nu) :
    pairCachedCoordinateSieveBool tau nu sieve (pairCoordinateSignature sieve x)
      (pairCoordinateSignature sieve y) = coordinateSquareSieveBool sieve (x * y + 1) := by
  induction sieve with
  | nil => rfl
  | cons item sieve ih =>
      rcases item with ⟨k, mask⟩
      change
        (pairResidueMaskBool tau nu k mask (pairCoordinateResidues k x)
          (pairCoordinateResidues k y) &&
          pairCachedCoordinateSieveBool tau nu sieve (pairCoordinateSignature sieve x)
            (pairCoordinateSignature sieve y)) =
        (coordinateSquareMaskBool k mask (x * y + 1) &&
          coordinateSquareSieveBool sieve (x * y + 1))
      rw [pairResidueMaskBool_coordinates, ih]















end D1Bound5
end
