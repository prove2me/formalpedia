-- Prove2me | solution 1 for D1Bound5.firstPairGeometryRowsAt_covers_1_3
-- status  : ACCEPTED   (prove)
-- author  : @tp
-- created : 2026-10-24T04:40:37.365868+00:00
-- url     : https://prove2.me/submissions/15248a8e-8946-43c2-8822-685c2ca1e1d0

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
    firstPairRepresentatives_1_3 ⊆ (firstPairGeometryRowsAt 1 3).toFinset := by
  decide +kernel







end D1Bound5
end
