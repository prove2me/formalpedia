-- Prove2me | solution 1 for D1Bound5.firstPairTable_0_6_third_rows
-- status  : ACCEPTED   (prove)
-- author  : @tp
-- created : 2026-10-23T23:45:09.598911+00:00
-- url     : https://prove2.me/submissions/8624e922-e891-45ad-a69a-81b20d6d7df5

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
import Theorems.Thm_D1Bound5_firstPairTable_0_6_orbits
import Theorems.Thm_D1Bound5_oneSmallThirdRows_27_complete
import Theorems.Thm_D1Bound5_oneSmallThirdRows_28_complete
import Theorems.Thm_D1Bound5_oneSmallThirdRows_of_table_orbits

section
namespace D1Bound5
open QuadInt







theorem _root_.solution (a b s : QuadInt 0 6)
    (hrow : firstPairCoordinates a b ∈ firstPairTable 0 6)
    (hbound : s.norm ≤ 224) (horder : b.norm ≤ s.norm)
    (ha : s ≠ a) (hb : s ≠ b) (hpair : PairExtension a b s) :
    OneSmallNormalizedThirdRows a b s := by
  apply oneSmallThirdRows_of_table_orbits firstPairs_0_6
    firstPairRepresentatives_0_6 firstPairTable_0_6_orbits ?_ a b s
    (by simpa [firstPairTable] using hrow) hbound horder ha hb hpair
  intro rep hrep
  simp only [firstPairRepresentatives_0_6, Finset.mem_insert, Finset.mem_singleton] at hrep
  rcases hrep with rfl | rfl
  · exact oneSmallThirdRows_27_complete
  · exact oneSmallThirdRows_28_complete















end D1Bound5
end
