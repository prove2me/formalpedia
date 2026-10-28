-- Prove2me | solution 1 for D1Bound5.tailDisk_1_13_eq
-- status  : ACCEPTED   (prove)
-- author  : @tp
-- created : 2026-10-24T04:27:18.881316+00:00
-- url     : https://prove2.me/submissions/5feb64f8-6579-4345-8873-4e0c01a1ec50

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
theorem _root_.solution : disk 1 13 15 = tailDisk_1_13.toFinset := by
  decide +kernel























end D1Bound5
end
