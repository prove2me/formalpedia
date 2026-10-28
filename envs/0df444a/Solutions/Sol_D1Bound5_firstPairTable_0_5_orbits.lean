-- Prove2me | solution 1 for D1Bound5.firstPairTable_0_5_orbits
-- status  : ACCEPTED   (prove)
-- author  : @tp
-- created : 2026-10-24T05:02:09.687254+00:00
-- url     : https://prove2.me/submissions/9f028194-8402-4bfe-a216-3ae189cdf272

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
    firstPairs_0_5.toFinset = firstPairRepresentatives_0_5.biUnion (firstPairOrbit 0) := by
  decide +kernel































































































end D1Bound5
end
