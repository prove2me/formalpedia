-- Prove2me | solution 1 for D1Bound5.PairGraphPrepared22.indexed_chunk06_checked
-- status  : ACCEPTED   (prove)
-- author  : @tp
-- created : 2026-10-24T05:38:48.920891+00:00
-- url     : https://prove2.me/submissions/0ee919de-5ffb-481c-b039-442a2b6eceb8

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
import Definitions.Def_D1Bound5_SmallPairGraphInputs22_Definitions_001
import Definitions.Def_D1Bound5_SmallPairGraphInputs22_Definitions_002
import Definitions.Def_D1Bound5_SmallPairGraphWitnessData22_Definitions_001
import Definitions.Def_D1Bound5_SmallPairGraphWitnessData22_Definitions_003

section
namespace D1Bound5.PairGraphPrepared22
set_option autoImplicit false
set_option maxRecDepth 100000
set_option maxHeartbeats 0

/-- Full original vertex list and both signs; only aligned row lists are sliced. -/
theorem _root_.solution :
    pairIndexedWitnessesPrefixBool smallPairA_22 smallPairB_22 anchorRoot
      (10^1100) smallPairClosure_22 128
      (witnesses.drop 640) (destinations.drop 640) = true := by
  decide +kernel

end D1Bound5.PairGraphPrepared22
end
