-- Prove2me | solution 1 for D1Bound5.firstPairCoordinates_eq
-- status  : ACCEPTED   (prove)
-- author  : @tp
-- created : 2026-10-24T05:02:22.306316+00:00
-- url     : https://prove2.me/submissions/9c01a74d-9c7f-4e7e-b6b0-04278ca176a9

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
import Definitions.Def_D1Bound5_OneSmallFiniteCheck_Definitions
import Definitions.Def_D1Bound5_OneSmallRows_Definitions

section
namespace D1Bound5
open QuadInt





theorem _root_.solution {tau nu : ℤ} (a b a' b' : QuadInt tau nu)
    (h : firstPairCoordinates a b = firstPairCoordinates a' b') : a = a' ∧ b = b' := by
  constructor
  · apply QuadraticAlgebra.ext
    · exact congrArg (fun p => p.1.1) h
    · exact congrArg (fun p => p.1.2) h
  · apply QuadraticAlgebra.ext
    · exact congrArg (fun p => p.2.1) h
    · exact congrArg (fun p => p.2.2) h









end D1Bound5
end
