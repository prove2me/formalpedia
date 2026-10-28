-- Prove2me | solution 1 for D1Bound5.PairGraphPrepared32.indexed_checked
-- status  : ACCEPTED   (prove)
-- author  : @tp
-- created : 2026-10-24T05:13:53.846986+00:00
-- url     : https://prove2.me/submissions/97b1978f-8be4-4322-b84a-b72bd89e6be2

import Mathlib.Algebra.QuadraticAlgebra.Basic
import Mathlib.Algebra.Ring.Basic
import Mathlib.Algebra.Ring.Equiv
import Mathlib.Data.Finset.Card
import Mathlib.Data.Finset.Prod
import Mathlib.Data.Int.Interval
import Mathlib.Data.Int.Sqrt
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.LinearCombination
import Definitions.Def_D1Bound5_PairClosureIndexedWitness_Definitions
import Definitions.Def_D1Bound5_SmallPairGraphInputs32_Definitions
import Definitions.Def_D1Bound5_SmallPairGraphWitnessData32_Definitions

section
namespace D1Bound5
set_option maxRecDepth 100000
set_option maxHeartbeats 0

open PairGraphPrepared32

theorem _root_.solution :
    pairClosureIndexedWitnessBool smallPairA_32 smallPairB_32 anchorRoot
      (10^1100) smallPairClosure_32 witnesses destinations = true := by
  decide +kernel



end D1Bound5
end
