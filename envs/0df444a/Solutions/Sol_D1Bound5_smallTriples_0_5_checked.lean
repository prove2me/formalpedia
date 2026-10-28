-- Prove2me | solution 1 for D1Bound5.smallTriples_0_5_checked
-- status  : ACCEPTED   (prove)
-- author  : @tp
-- created : 2026-10-24T05:34:57.834151+00:00
-- url     : https://prove2.me/submissions/140f46df-e3dc-4a0d-8072-e2ec0c26ec65

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
import Definitions.Def_D1Bound5_SmallQuadrupleData_Definitions
import Definitions.Def_D1Bound5_SmallTripleCheck_Definitions
import Definitions.Def_D1Bound5_SmallTripleData_Definitions

section
namespace D1Bound5
open QuadInt
set_option maxRecDepth 32768
set_option maxHeartbeats 6000000










































theorem _root_.solution :
    smallTripleClassifiedBool smallDisk_0_5 (smallTripleTable 0 5) = true := by
  decide +kernel

















































end D1Bound5
end
