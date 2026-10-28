-- Prove2me | solution 1 for D1Bound5.tailDisk_0_2_checked
-- status  : ACCEPTED   (prove)
-- author  : @tp
-- created : 2026-10-24T05:44:25.950115+00:00
-- url     : https://prove2.me/submissions/4b3165e0-07fa-4218-81d8-3b1db8790e60

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
import Definitions.Def_D1Bound5_SmallTailAllData_Definitions
import Definitions.Def_D1Bound5_SmallTailExplicit_Definitions

section
namespace D1Bound5
open QuadInt
set_option maxRecDepth 32768
set_option maxHeartbeats 6000000





/-- No external execution or native-evaluation axiom is used. -/
theorem _root_.solution : tailListBool tailDisk_0_2 = true := by
  decide +kernel





























































































































































































































end D1Bound5
end
