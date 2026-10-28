-- Prove2me | solution 1 for D1Bound5.firstPairTable_1_5_third_rows
-- status  : ACCEPTED   (prove)
-- author  : @tp
-- created : 2026-10-23T23:40:25.191702+00:00
-- url     : https://prove2.me/submissions/fd3f5d0d-7600-4f41-b2b9-03f1d83c3059

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
import Definitions.Def_D1Bound5_FirstPairData_Definitions
import Definitions.Def_D1Bound5_OneSmallFiniteCheck_Definitions
import Definitions.Def_D1Bound5_OneSmallRows_Definitions
import Definitions.Def_D1Bound5_OneSmallSymmetry_Definitions
import Definitions.Def_D1Bound5_PairExtensionCore_Definitions
import Theorems.Thm_D1Bound5_firstPairTable_1_5_orbits
import Theorems.Thm_D1Bound5_oneSmallThirdRows_35_complete
import Theorems.Thm_D1Bound5_oneSmallThirdRows_36_complete
import Theorems.Thm_D1Bound5_oneSmallThirdRows_of_table_orbits

section
namespace D1Bound5
open QuadInt

















theorem _root_.solution (a b s : QuadInt 1 5)
    (hrow : firstPairCoordinates a b ∈ firstPairTable 1 5)
    (hbound : s.norm ≤ 224) (horder : b.norm ≤ s.norm)
    (ha : s ≠ a) (hb : s ≠ b) (hpair : PairExtension a b s) :
    OneSmallNormalizedThirdRows a b s := by
  apply oneSmallThirdRows_of_table_orbits firstPairs_1_5
    firstPairRepresentatives_1_5 firstPairTable_1_5_orbits ?_ a b s
    (by simpa [firstPairTable] using hrow) hbound horder ha hb hpair
  intro rep hrep
  simp only [firstPairRepresentatives_1_5, Finset.mem_insert, Finset.mem_singleton] at hrep
  rcases hrep with rfl | rfl
  · exact oneSmallThirdRows_35_complete
  · exact oneSmallThirdRows_36_complete





end D1Bound5
end
