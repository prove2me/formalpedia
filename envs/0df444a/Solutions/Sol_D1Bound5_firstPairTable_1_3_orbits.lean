-- Prove2me | solution 1 for D1Bound5.firstPairTable_1_3_orbits
-- status  : ACCEPTED   (prove)
-- author  : @tp
-- created : 2026-10-24T04:55:44.105164+00:00
-- url     : https://prove2.me/submissions/0a19591b-4565-470b-80ef-dc2c1e81888f

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
    firstPairs_1_3.toFinset = firstPairRepresentatives_1_3.biUnion (firstPairOrbit 1) := by
  decide +kernel















































































end D1Bound5
end
