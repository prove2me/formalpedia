-- Prove2me | solution 1 for D1Bound5.firstPair_1_6_checked
-- status  : ACCEPTED   (prove)
-- author  : @tp
-- created : 2026-10-24T04:24:01.844371+00:00
-- url     : https://prove2.me/submissions/fc56aa85-f69e-4573-8329-7661d034f013

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
import Definitions.Def_D1Bound5_Coordinates_Definitions
import Definitions.Def_D1Bound5_FirstPairData_Definitions
import Definitions.Def_D1Bound5_OneSmallFiniteCheck_Definitions
import Definitions.Def_D1Bound5_SmallQuadrupleData_Definitions

section
namespace D1Bound5
open QuadInt
set_option maxRecDepth 32768
set_option maxHeartbeats 12000000

































































































































theorem _root_.solution :
    firstPairClassifiedBool smallDisk_1_6 smallDisk_1_6 (firstPairTable 1 6) = true := by
  decide +kernel













end D1Bound5
end
