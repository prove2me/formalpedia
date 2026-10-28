-- Prove2me | solution 1 for D1Bound5.smallTriple_classified_0_7
-- status  : ACCEPTED   (prove)
-- author  : @tp
-- created : 2026-10-24T00:39:53.928972+00:00
-- url     : https://prove2.me/submissions/ace41194-8cc1-4db6-b8f1-f672cdd7ca01

import Mathlib.Algebra.QuadraticAlgebra.Basic
import Mathlib.Algebra.Ring.Basic
import Mathlib.Algebra.Ring.Equiv
import Mathlib.Data.Finset.Card
import Mathlib.Data.Finset.Prod
import Mathlib.Data.Int.Interval
import Mathlib.Data.Int.Sqrt
import Mathlib.Tactic.IntervalCases
import Mathlib.Tactic.Linarith
import Definitions.Def_D1Bound5_Coordinates_Definitions
import Definitions.Def_D1Bound5_DiskEnumeration_Definitions
import Definitions.Def_D1Bound5_IsD1Tuple
import Definitions.Def_D1Bound5_SmallQuadrupleData_Definitions
import Definitions.Def_D1Bound5_SmallTripleCheck_Definitions
import Definitions.Def_D1Bound5_SmallTripleData_Definitions
import Theorems.Thm_D1Bound5_smallDisk_0_7_eq
import Theorems.Thm_D1Bound5_smallTripleClassified_of_explicit_list
import Theorems.Thm_D1Bound5_smallTriples_0_7_checked

section
namespace D1Bound5
open QuadInt
set_option maxRecDepth 32768
set_option maxHeartbeats 6000000




















































theorem _root_.solution
    (t : Fin 3 → QuadInt 0 7) (ht : IsD1Tuple t)
    (hnorm : ∀ i, (t i).norm ≤ 8) :
    tripleCoordinates (t 0) (t 1) (t 2) ∈ smallTripleTable 0 7 := by
  apply smallTripleClassified_of_explicit_list (by decide) smallDisk_0_7
    (smallTripleTable 0 7) ?_ smallTriples_0_7_checked t ht hnorm
  intro z hz
  rw [smallDisk_0_7_eq, List.mem_toFinset] at hz
  exact hz







































end D1Bound5
end
