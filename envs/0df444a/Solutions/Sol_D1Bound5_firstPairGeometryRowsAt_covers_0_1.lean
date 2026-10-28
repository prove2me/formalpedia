-- Prove2me | solution 1 for D1Bound5.firstPairGeometryRowsAt_covers_0_1
-- status  : ACCEPTED   (prove)
-- author  : @tp
-- created : 2026-10-24T05:57:25.892277+00:00
-- url     : https://prove2.me/submissions/cb3a7f44-3266-4a61-a36c-c0d4c5a27e90

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
import Definitions.Def_D1Bound5_FirstPairGeometryData_Definitions_002

section
namespace D1Bound5
open QuadInt



namespace FirstPairGeometryRow






























end FirstPairGeometryRow

set_option maxHeartbeats 0
set_option maxRecDepth 100000











































































































































































theorem _root_.solution :
    firstPairRepresentatives_0_1 ⊆ (firstPairGeometryRowsAt 0 1).toFinset := by
  decide +kernel



















end D1Bound5
end
