-- Prove2me | solution 1 for D1Bound5.smallPair_classified_0_5
-- status  : ACCEPTED   (prove)
-- author  : @tp
-- created : 2026-10-24T00:35:37.820558+00:00
-- url     : https://prove2.me/submissions/f7dab8d5-5d03-4e3c-b2cb-6ec5379126f2

import Mathlib.Algebra.QuadraticAlgebra.Basic
import Mathlib.Algebra.Ring.Basic
import Mathlib.Algebra.Ring.Equiv
import Mathlib.Analysis.Complex.Norm
import Mathlib.Data.Fin.Tuple.Sort
import Mathlib.Data.Finset.Card
import Mathlib.Data.Finset.Prod
import Mathlib.Data.Fintype.EquivFin
import Mathlib.Data.Int.GCD
import Mathlib.Data.Int.Interval
import Mathlib.Data.Int.Sqrt
import Mathlib.LinearAlgebra.Dimension.Free
import Mathlib.NumberTheory.NumberField.InfinitePlace.TotallyRealComplex
import Mathlib.NumberTheory.NumberField.Norm
import Mathlib.Tactic.IntervalCases
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.LinearCombination
import Definitions.Def_D1Bound5_Coordinates_Definitions
import Definitions.Def_D1Bound5_DiskEnumeration_Definitions
import Definitions.Def_D1Bound5_SmallPairClassificationCheck_Definitions
import Definitions.Def_D1Bound5_SmallPairClassificationData_Definitions
import Definitions.Def_D1Bound5_SmallQuadrupleData_Definitions
import Theorems.Thm_D1Bound5_smallDisk_0_5_eq
import Theorems.Thm_D1Bound5_smallPairClassified_of_explicit_list
import Theorems.Thm_D1Bound5_smallPairs_0_5_checked

section
namespace D1Bound5
open QuadInt
set_option maxRecDepth 32768
set_option maxHeartbeats 6000000

































































































theorem _root_.solution
    (a b : QuadInt 0 5) (ha : a ≠ 0) (hb : b ≠ 0) (hab : a ≠ b)
    (hroot : ∃ r, r*r = a*b+1) (hnondeg : a*b+1 ≠ 0)
    (hNa : a.norm ≤ 8) (hNb : b.norm ≤ 8) :
    pairCoordinates a b ∈ smallPairTable 0 5 := by
  apply smallPairClassified_of_explicit_list (by decide) smallDisk_0_5
    (smallPairTable 0 5) ?_ smallPairs_0_5_checked a b ha hb hab hroot hnondeg hNa hNb
  intro z hz
  rw [smallDisk_0_5_eq, List.mem_toFinset] at hz
  exact hz















































end D1Bound5
end
