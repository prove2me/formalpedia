-- Prove2me | solution 1 for D1Bound5.tailDisk_0_11_eq
-- status  : ACCEPTED   (prove)
-- author  : @tp
-- created : 2026-10-24T05:27:50.629311+00:00
-- url     : https://prove2.me/submissions/c240d1cb-afdf-4064-a8e6-48d522f4821c

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
theorem _root_.solution : disk 0 11 15 = tailDisk_0_11.toFinset := by
  decide +kernel























































































































































end D1Bound5
end
