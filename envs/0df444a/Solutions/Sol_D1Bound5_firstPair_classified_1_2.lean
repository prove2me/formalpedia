-- Prove2me | solution 1 for D1Bound5.firstPair_classified_1_2
-- status  : ACCEPTED   (prove)
-- author  : @tp
-- created : 2026-10-24T00:21:32.282134+00:00
-- url     : https://prove2.me/submissions/57b5c0a8-ed12-4489-b1d2-fcf059e28c32

import Mathlib.Algebra.QuadraticAlgebra.Basic
import Mathlib.Algebra.Ring.Basic
import Mathlib.Algebra.Ring.Equiv
import Mathlib.Data.Finset.Card
import Mathlib.Data.Finset.Prod
import Mathlib.Data.Int.Interval
import Mathlib.Data.Int.Sqrt
import Mathlib.Tactic.IntervalCases
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.LinearCombination
import Definitions.Def_D1Bound5_Coordinates_Definitions
import Definitions.Def_D1Bound5_DiskEnumeration_Definitions
import Definitions.Def_D1Bound5_FirstPairData_Definitions
import Definitions.Def_D1Bound5_OneSmallFiniteCheck_Definitions
import Definitions.Def_D1Bound5_SmallQuadrupleData_Definitions
import Theorems.Thm_D1Bound5_firstPairClassified_of_checked
import Theorems.Thm_D1Bound5_firstPair_1_2_checked
import Theorems.Thm_D1Bound5_smallDisk_1_2_eq

section
namespace D1Bound5
open QuadInt
set_option maxRecDepth 32768
set_option maxHeartbeats 12000000



















































































































theorem _root_.solution
    (a b : QuadInt 1 2) (hnorm : FirstPairNorms a b) (hroot : ∃ q, q*q = a*b+1) :
    (a = 1 ∧ b = 3) ∨ (a = -1 ∧ b = -3) ∨ firstPairCoordinates a b ∈ firstPairTable 1 2 := by
  apply firstPairClassified_of_checked (by decide) smallDisk_1_2 smallDisk_1_2
    (firstPairTable 1 2) ?_ ?_ firstPair_1_2_checked a b hnorm hroot
  all_goals intro q hq; rw [smallDisk_1_2_eq, List.mem_toFinset] at hq; exact hq



























end D1Bound5
end
