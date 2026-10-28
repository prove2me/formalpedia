-- Prove2me | solution 1 for D1Bound5.firstPairGeometryRowsAt_covers_0_5
-- status  : ACCEPTED   (prove)
-- author  : @tp
-- created : 2026-10-24T05:54:55.463569+00:00
-- url     : https://prove2.me/submissions/caddb555-d8c2-40bf-adce-d1636494a789

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
    firstPairRepresentatives_0_5 ⊆ (firstPairGeometryRowsAt 0 5).toFinset := by
  decide +kernel















end D1Bound5
end
