-- Prove2me | solution 1 for D1Bound5.smallExtensionSymmetry_norm
-- status  : ACCEPTED   (prove)
-- author  : @tp
-- created : 2026-10-24T04:55:17.723292+00:00
-- url     : https://prove2.me/submissions/a93c0a81-fa3b-4979-8a0e-180d65f6c700

import Mathlib.Algebra.Group.Int.Units
import Mathlib.Algebra.Polynomial.Monic
import Mathlib.Algebra.QuadraticAlgebra.Basic
import Mathlib.Algebra.Ring.Basic
import Mathlib.Algebra.Ring.Equiv
import Mathlib.Algebra.Squarefree.Basic
import Mathlib.Analysis.Complex.Basic
import Mathlib.Analysis.Complex.Norm
import Mathlib.Analysis.Complex.Polynomial.Basic
import Mathlib.Data.Fin.Tuple.Sort
import Mathlib.Data.Finset.Card
import Mathlib.Data.Finset.Prod
import Mathlib.Data.Fintype.EquivFin
import Mathlib.Data.Int.GCD
import Mathlib.Data.Int.Interval
import Mathlib.Data.Int.Sqrt
import Mathlib.Data.List.Range
import Mathlib.LinearAlgebra.Dimension.Free
import Mathlib.NumberTheory.NumberField.InfinitePlace.TotallyRealComplex
import Mathlib.NumberTheory.NumberField.Norm
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.IntervalCases
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.LinearCombination
import Mathlib.Tactic.Ring
import Definitions.Def_D1Bound5_Coordinates_Definitions
import Definitions.Def_D1Bound5_SmallExtensionSymmetry_Definitions

section
open scoped NumberField
open Module

namespace D1Bound5
open QuadInt















theorem _root_.solution {tau nu : ℤ} (sgn conj : Bool)
    (z : QuadInt tau nu) : (smallExtensionSymmetry sgn conj z).norm = z.norm := by
  cases sgn <;> cases conj <;>
    simp [smallExtensionSymmetry, QuadraticAlgebra.norm_neg, QuadraticAlgebra.norm_star]











end D1Bound5
end
