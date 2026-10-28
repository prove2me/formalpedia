-- Prove2me | solution 1 for D1Bound5.PairGraphPrepared26.indexed_tail128_checked
-- status  : ACCEPTED   (prove)
-- author  : @tp
-- created : 2026-10-24T05:19:22.588037+00:00
-- url     : https://prove2.me/submissions/89b6187e-fc12-4482-82b3-107224c021ee

import Mathlib.Algebra.QuadraticAlgebra.Basic
import Mathlib.Algebra.Ring.Basic
import Mathlib.Algebra.Ring.Equiv
import Mathlib.Data.Finset.Card
import Mathlib.Data.Finset.Prod
import Mathlib.Data.Int.Interval
import Mathlib.Data.Int.Sqrt
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.LinearCombination
import Definitions.Def_D1Bound5_PairClosureIndexedChunks_Definitions
import Definitions.Def_D1Bound5_PairClosureWitness_Definitions
import Definitions.Def_D1Bound5_SmallPairGraphInputs26_Definitions_001
import Definitions.Def_D1Bound5_SmallPairGraphInputs26_Definitions_002
import Definitions.Def_D1Bound5_SmallPairGraphWitnessData26_Definitions_001
import Definitions.Def_D1Bound5_SmallPairGraphWitnessData26_Definitions_003

section
namespace D1Bound5.PairGraphPrepared26
set_option autoImplicit false
set_option maxRecDepth 100000
set_option maxHeartbeats 0

/-- Tail pilot: exactly rows 1397 through 1524, with original global destinations. -/
theorem _root_.solution :
    pairIndexedWitnessesPrefixBool smallPairA_26 smallPairB_26 anchorRoot
      (10^1100) smallPairClosure_26 128
      (witnesses.drop 1397) (destinations.drop 1397) = true := by
  decide +kernel

end D1Bound5.PairGraphPrepared26
end
