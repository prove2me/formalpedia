-- Prove2me | solution 1 for D1Bound5.smallTriple_classified_1_4
-- status  : ACCEPTED   (prove)
-- author  : @tp
-- created : 2026-10-24T00:40:00.03798+00:00
-- url     : https://prove2.me/submissions/799cf94c-9b60-49db-9948-91ddf191fded

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
import Theorems.Thm_D1Bound5_smallDisk_1_4_eq
import Theorems.Thm_D1Bound5_smallTripleClassified_of_explicit_list
import Theorems.Thm_D1Bound5_smallTriples_1_4_checked

section
namespace D1Bound5
open QuadInt
set_option maxRecDepth 32768
set_option maxHeartbeats 6000000








































































theorem _root_.solution
    (t : Fin 3 → QuadInt 1 4) (ht : IsD1Tuple t)
    (hnorm : ∀ i, (t i).norm ≤ 8) :
    tripleCoordinates (t 0) (t 1) (t 2) ∈ smallTripleTable 1 4 := by
  apply smallTripleClassified_of_explicit_list (by decide) smallDisk_1_4
    (smallTripleTable 1 4) ?_ smallTriples_1_4_checked t ht hnorm
  intro z hz
  rw [smallDisk_1_4_eq, List.mem_toFinset] at hz
  exact hz



















end D1Bound5
end
