-- Prove2me | solution 1 for D1Bound5.tailDisk_0_1_eq
-- status  : ACCEPTED   (prove)
-- author  : @tp
-- created : 2026-10-24T05:42:07.89125+00:00
-- url     : https://prove2.me/submissions/6b8d3b95-18d1-4e9a-b22f-5fa115c1e5b1

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
import Definitions.Def_D1Bound5_SmallTailData0_1_Definitions

section
namespace D1Bound5
open QuadInt
set_option maxRecDepth 32768
set_option maxHeartbeats 6000000



/-- Kernel-checked equality with the proved exhaustive disk enumeration. -/
theorem _root_.solution : disk 0 1 15 = tailDisk_0_1.toFinset := by
  decide +kernel





end D1Bound5
end
