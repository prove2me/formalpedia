-- Prove2me | solution 1 for D1Bound5.firstPair_classified_1_3
-- status  : ACCEPTED   (prove)
-- author  : @tp
-- created : 2026-10-24T00:21:23.68082+00:00
-- url     : https://prove2.me/submissions/cfa9fa5c-6ef9-43eb-ab11-d9bbf7192d75

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
import Theorems.Thm_D1Bound5_firstPair_1_3_checked
import Theorems.Thm_D1Bound5_smallDisk_1_3_eq

section
namespace D1Bound5
open QuadInt
set_option maxRecDepth 32768
set_option maxHeartbeats 12000000























































































































theorem _root_.solution
    (a b : QuadInt 1 3) (hnorm : FirstPairNorms a b) (hroot : ∃ q, q*q = a*b+1) :
    (a = 1 ∧ b = 3) ∨ (a = -1 ∧ b = -3) ∨ firstPairCoordinates a b ∈ firstPairTable 1 3 := by
  apply firstPairClassified_of_checked (by decide) smallDisk_1_3 smallDisk_1_3
    (firstPairTable 1 3) ?_ ?_ firstPair_1_3_checked a b hnorm hroot
  all_goals intro q hq; rw [smallDisk_1_3_eq, List.mem_toFinset] at hq; exact hq























end D1Bound5
end
