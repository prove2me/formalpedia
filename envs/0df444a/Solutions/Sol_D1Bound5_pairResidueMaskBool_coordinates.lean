-- Prove2me | solution 1 for D1Bound5.pairResidueMaskBool_coordinates
-- status  : ACCEPTED   (prove)
-- author  : @tp
-- created : 2026-10-24T05:41:44.804066+00:00
-- url     : https://prove2.me/submissions/4ec4a752-6e1f-4e64-8710-df420bdfb359

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

section
namespace D1Bound5





/-- This is equality of the actual computational mask predicates; no
primality, mask-validity, nonzero, or square-root assumption is used. -/
theorem _root_.solution {tau nu : ℤ} (k mask : ℕ)
    (x y : QuadInt tau nu) :
    pairResidueMaskBool tau nu k mask (pairCoordinateResidues k x)
      (pairCoordinateResidues k y) = coordinateSquareMaskBool k mask (x * y + 1) := by
  simp only [pairResidueMaskBool, pairCoordinateResidues, coordinateSquareMaskBool,
    ZMod.natCast_zmod_val, QuadraticAlgebra.re_add, QuadraticAlgebra.im_add,
    QuadraticAlgebra.re_mul, QuadraticAlgebra.im_mul,
    QuadraticAlgebra.re_one, QuadraticAlgebra.im_one,
    Int.cast_add, Int.cast_mul, Int.cast_neg, Int.cast_one, Int.cast_zero, add_zero]





















end D1Bound5
end
