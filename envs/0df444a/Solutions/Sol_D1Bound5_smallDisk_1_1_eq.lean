-- Prove2me | solution 1 for D1Bound5.smallDisk_1_1_eq
-- status  : ACCEPTED   (prove)
-- author  : @tp
-- created : 2026-10-24T05:00:13.853039+00:00
-- url     : https://prove2.me/submissions/96a6e4f8-6398-40c6-9043-eeec40f79c9b

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
import Definitions.Def_D1Bound5_SmallQuadrupleData_Definitions

section
namespace D1Bound5
open QuadInt
set_option maxRecDepth 32768
set_option maxHeartbeats 6000000



































































theorem _root_.solution : disk 1 1 8 = smallDisk_1_1.toFinset := by
  decide +kernel































































end D1Bound5
end
