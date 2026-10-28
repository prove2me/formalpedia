-- Prove2me | solution 1 for D1Bound5.smallTriples_1_1_checked
-- status  : ACCEPTED   (prove)
-- author  : @tp
-- created : 2026-10-24T05:53:36.349291+00:00
-- url     : https://prove2.me/submissions/30f446e1-f9b7-4f31-a427-bb93e4d1d8cd

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
    smallTripleClassifiedBool smallDisk_1_1 (smallTripleTable 1 1) = true := by
  decide +kernel

































end D1Bound5
end
