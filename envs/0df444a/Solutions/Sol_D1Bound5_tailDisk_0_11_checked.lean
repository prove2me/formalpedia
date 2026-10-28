-- Prove2me | solution 1 for D1Bound5.tailDisk_0_11_checked
-- status  : ACCEPTED   (prove)
-- author  : @tp
-- created : 2026-10-24T05:48:38.18401+00:00
-- url     : https://prove2.me/submissions/5a3e27e2-0612-4834-8f2f-e86f97dbb0d2

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
theorem _root_.solution : tailListBool tailDisk_0_11 = true := by
  decide +kernel





















































































































































end D1Bound5
end
