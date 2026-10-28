-- Prove2me | solution 1 for D1Bound5.smallTripleSeeds_3_checked
-- status  : ACCEPTED   (prove)
-- author  : @tp
-- created : 2026-10-24T05:42:02.466987+00:00
-- url     : https://prove2.me/submissions/425a85da-a077-49eb-9c0b-619312ea4885

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
import Definitions.Def_D1Bound5_SmallTripleExtensionData3_Definitions

section
namespace D1Bound5
open QuadInt
set_option maxRecDepth 32768
set_option maxHeartbeats 8000000









theorem _root_.solution :
    pairSeedsCoveredBool smallTripleAnchorA_3 smallTripleAnchorB_3
      seedRootDisk_0_1 smallTriplePairClosure_3 = true := by
  decide +kernel







end D1Bound5
end
