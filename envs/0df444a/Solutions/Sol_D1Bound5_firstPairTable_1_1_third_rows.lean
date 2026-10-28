-- Prove2me | solution 1 for D1Bound5.firstPairTable_1_1_third_rows
-- status  : ACCEPTED   (prove)
-- author  : @tp
-- created : 2026-10-23T23:45:53.32746+00:00
-- url     : https://prove2.me/submissions/ac389824-2ea6-468e-920b-a63546303503

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
import Theorems.Thm_D1Bound5_firstPairTable_1_1_orbits
import Theorems.Thm_D1Bound5_oneSmallThirdRows_10_complete
import Theorems.Thm_D1Bound5_oneSmallThirdRows_11_complete
import Theorems.Thm_D1Bound5_oneSmallThirdRows_12_complete
import Theorems.Thm_D1Bound5_oneSmallThirdRows_13_complete
import Theorems.Thm_D1Bound5_oneSmallThirdRows_14_complete
import Theorems.Thm_D1Bound5_oneSmallThirdRows_15_complete
import Theorems.Thm_D1Bound5_oneSmallThirdRows_16_complete
import Theorems.Thm_D1Bound5_oneSmallThirdRows_17_complete
import Theorems.Thm_D1Bound5_oneSmallThirdRows_18_complete
import Theorems.Thm_D1Bound5_oneSmallThirdRows_19_complete
import Theorems.Thm_D1Bound5_oneSmallThirdRows_20_complete
import Theorems.Thm_D1Bound5_oneSmallThirdRows_21_complete
import Theorems.Thm_D1Bound5_oneSmallThirdRows_22_complete
import Theorems.Thm_D1Bound5_oneSmallThirdRows_23_complete
import Theorems.Thm_D1Bound5_oneSmallThirdRows_24_complete
import Theorems.Thm_D1Bound5_oneSmallThirdRows_of_table_orbits

section
namespace D1Bound5
open QuadInt









theorem _root_.solution (a b s : QuadInt 1 1)
    (hrow : firstPairCoordinates a b ∈ firstPairTable 1 1)
    (hbound : s.norm ≤ 224) (horder : b.norm ≤ s.norm)
    (ha : s ≠ a) (hb : s ≠ b) (hpair : PairExtension a b s) :
    OneSmallNormalizedThirdRows a b s := by
  apply oneSmallThirdRows_of_table_orbits firstPairs_1_1
    firstPairRepresentatives_1_1 firstPairTable_1_1_orbits ?_ a b s
    (by simpa [firstPairTable] using hrow) hbound horder ha hb hpair
  intro rep hrep
  simp only [firstPairRepresentatives_1_1, Finset.mem_insert, Finset.mem_singleton] at hrep
  rcases hrep with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact oneSmallThirdRows_10_complete
  · exact oneSmallThirdRows_11_complete
  · exact oneSmallThirdRows_12_complete
  · exact oneSmallThirdRows_13_complete
  · exact oneSmallThirdRows_14_complete
  · exact oneSmallThirdRows_15_complete
  · exact oneSmallThirdRows_16_complete
  · exact oneSmallThirdRows_17_complete
  · exact oneSmallThirdRows_18_complete
  · exact oneSmallThirdRows_19_complete
  · exact oneSmallThirdRows_20_complete
  · exact oneSmallThirdRows_21_complete
  · exact oneSmallThirdRows_22_complete
  · exact oneSmallThirdRows_23_complete
  · exact oneSmallThirdRows_24_complete













end D1Bound5
end
