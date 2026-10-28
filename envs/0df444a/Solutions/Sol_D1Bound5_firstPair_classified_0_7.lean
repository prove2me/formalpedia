-- Prove2me | solution 1 for D1Bound5.firstPair_classified_0_7
-- status  : ACCEPTED   (prove)
-- author  : @tp
-- created : 2026-10-24T00:27:42.458081+00:00
-- url     : https://prove2.me/submissions/758daa58-4d89-40fa-a3aa-303b3997d0ce

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
import Theorems.Thm_D1Bound5_firstPair_0_7_checked
import Theorems.Thm_D1Bound5_smallDisk_0_7_eq

section
namespace D1Bound5
open QuadInt
set_option maxRecDepth 32768
set_option maxHeartbeats 12000000







































































































theorem _root_.solution
    (a b : QuadInt 0 7) (hnorm : FirstPairNorms a b) (hroot : ∃ q, q*q = a*b+1) :
    (a = 1 ∧ b = 3) ∨ (a = -1 ∧ b = -3) ∨ firstPairCoordinates a b ∈ firstPairTable 0 7 := by
  apply firstPairClassified_of_checked (by decide) smallDisk_0_7 smallDisk_0_7
    (firstPairTable 0 7) ?_ ?_ firstPair_0_7_checked a b hnorm hroot
  all_goals intro q hq; rw [smallDisk_0_7_eq, List.mem_toFinset] at hq; exact hq







































end D1Bound5
end
