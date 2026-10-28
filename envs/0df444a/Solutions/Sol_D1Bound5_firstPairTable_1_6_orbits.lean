-- Prove2me | solution 1 for D1Bound5.firstPairTable_1_6_orbits
-- status  : ACCEPTED   (prove)
-- author  : @tp
-- created : 2026-10-24T05:15:55.88433+00:00
-- url     : https://prove2.me/submissions/92b502d6-1bcc-4f49-955b-9e6cb835059b

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

section
namespace D1Bound5
open QuadInt
set_option maxRecDepth 32768
set_option maxHeartbeats 12000000











































































theorem _root_.solution :
    firstPairs_1_6.toFinset = firstPairRepresentatives_1_6.biUnion (firstPairOrbit 1) := by
  decide +kernel



































































end D1Bound5
end
