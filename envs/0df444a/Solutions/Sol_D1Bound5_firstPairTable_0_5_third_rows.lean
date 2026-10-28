-- Prove2me | solution 1 for D1Bound5.firstPairTable_0_5_third_rows
-- status  : ACCEPTED   (prove)
-- author  : @tp
-- created : 2026-10-23T23:46:26.554501+00:00
-- url     : https://prove2.me/submissions/ce3d57ec-e71b-4e7a-be8f-273c3ee00831

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
import Theorems.Thm_D1Bound5_firstPairTable_0_5_orbits
import Theorems.Thm_D1Bound5_oneSmallThirdRows_25_complete
import Theorems.Thm_D1Bound5_oneSmallThirdRows_26_complete
import Theorems.Thm_D1Bound5_oneSmallThirdRows_of_table_orbits

section
namespace D1Bound5
open QuadInt





theorem _root_.solution (a b s : QuadInt 0 5)
    (hrow : firstPairCoordinates a b ∈ firstPairTable 0 5)
    (hbound : s.norm ≤ 224) (horder : b.norm ≤ s.norm)
    (ha : s ≠ a) (hb : s ≠ b) (hpair : PairExtension a b s) :
    OneSmallNormalizedThirdRows a b s := by
  apply oneSmallThirdRows_of_table_orbits firstPairs_0_5
    firstPairRepresentatives_0_5 firstPairTable_0_5_orbits ?_ a b s
    (by simpa [firstPairTable] using hrow) hbound horder ha hb hpair
  intro rep hrep
  simp only [firstPairRepresentatives_0_5, Finset.mem_insert, Finset.mem_singleton] at hrep
  rcases hrep with rfl | rfl
  · exact oneSmallThirdRows_25_complete
  · exact oneSmallThirdRows_26_complete

















end D1Bound5
end
