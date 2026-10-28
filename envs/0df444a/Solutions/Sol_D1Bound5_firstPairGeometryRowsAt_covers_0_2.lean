-- Prove2me | solution 1 for D1Bound5.firstPairGeometryRowsAt_covers_0_2
-- status  : ACCEPTED   (prove)
-- author  : @tp
-- created : 2026-10-24T05:55:07.085984+00:00
-- url     : https://prove2.me/submissions/fa8460dc-2e00-427b-8a7e-b34fc3a14cbf

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
    firstPairRepresentatives_0_2 ⊆ (firstPairGeometryRowsAt 0 2).toFinset := by
  decide +kernel

















end D1Bound5
end
