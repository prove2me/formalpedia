-- Prove2me | solution 1 for D1Bound5.smallTripleSeeds_10_checked
-- status  : ACCEPTED   (prove)
-- author  : @tp
-- created : 2026-10-24T05:29:12.596103+00:00
-- url     : https://prove2.me/submissions/f9ac8dc2-7dc7-4e64-bb2d-0b36aebf8b8c

import Mathlib.Algebra.QuadraticAlgebra.Basic
import Mathlib.Algebra.Ring.Basic
import Mathlib.Algebra.Ring.Equiv
import Mathlib.Data.Finset.Card
import Mathlib.Data.Finset.Prod
import Mathlib.Data.Int.Interval
import Mathlib.Data.Int.Sqrt
import Mathlib.Data.List.Range
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.LinearCombination
import Definitions.Def_D1Bound5_Coordinates_Definitions
import Definitions.Def_D1Bound5_PairExtensionCore_Definitions
import Definitions.Def_D1Bound5_PairSeedDisks_Definitions
import Definitions.Def_D1Bound5_SmallTripleExtensionData10_Definitions

section
namespace D1Bound5
open QuadInt
set_option maxRecDepth 32768
set_option maxHeartbeats 8000000









theorem _root_.solution :
    pairSeedsCoveredBool smallTripleAnchorA_10 smallTripleAnchorB_10
      seedRootDisk_1_2 smallTriplePairClosure_10 = true := by
  decide +kernel







end D1Bound5
end
