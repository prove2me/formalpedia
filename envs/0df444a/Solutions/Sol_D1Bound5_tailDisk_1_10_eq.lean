-- Prove2me | solution 1 for D1Bound5.tailDisk_1_10_eq
-- status  : ACCEPTED   (prove)
-- author  : @tp
-- created : 2026-10-24T05:33:49.564052+00:00
-- url     : https://prove2.me/submissions/72b52247-e87f-4c71-b3d3-a57140ae5ae0

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
import Mathlib.Tactic.Ring
import Definitions.Def_D1Bound5_Coordinates_Definitions
import Definitions.Def_D1Bound5_DiskEnumeration_Definitions
import Definitions.Def_D1Bound5_SmallTailAllData_Definitions

section
namespace D1Bound5
open QuadInt
set_option maxRecDepth 32768
set_option maxHeartbeats 6000000



















































































































































































/-- Kernel-checked equality with the proved exhaustive disk enumeration. -/
theorem _root_.solution : disk 1 10 15 = tailDisk_1_10.toFinset := by
  decide +kernel















































end D1Bound5
end
