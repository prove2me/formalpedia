-- Prove2me | solution 1 for D1Bound5.smallTripleTable_orbits
-- status  : ACCEPTED   (prove)
-- author  : @tp
-- created : 2026-10-24T04:48:16.386836+00:00
-- url     : https://prove2.me/submissions/6151cf2c-4191-4194-b93d-a76f9ab1f6c0

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
import Definitions.Def_D1Bound5_SmallTripleData_Definitions

section
namespace D1Bound5
open QuadInt
set_option maxRecDepth 32768
set_option maxHeartbeats 6000000


















/-- Exact agreement between the explicit 24 triples and the ten manuscript
orbits. The half-integral models use ω=(1+sqrt(-d))/2. -/
theorem _root_.solution :
    smallTriples_0_1.toFinset = smallTripleRepresentatives_0_1.biUnion (smallTripleOrbit 0) ∧
    smallTriples_0_2.toFinset = smallTripleRepresentatives_0_2.biUnion (smallTripleOrbit 0) ∧
    smallTriples_1_1.toFinset = smallTripleRepresentatives_1_1.biUnion (smallTripleOrbit 1) ∧
    smallTriples_1_2.toFinset = smallTripleRepresentatives_1_2.biUnion (smallTripleOrbit 1) := by
  decide +kernel









































































end D1Bound5
end
