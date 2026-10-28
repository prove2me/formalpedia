-- Prove2me | solution 1 for D1Bound5.PairGraphPrepared27.indexed_checked
-- status  : ACCEPTED   (prove)
-- author  : @tp
-- created : 2026-10-24T04:59:26.715292+00:00
-- url     : https://prove2.me/submissions/6b5511d0-0647-4875-a518-693d1fd7ee26

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
import Definitions.Def_D1Bound5_SmallPairGraphInputs27_Definitions_001
import Definitions.Def_D1Bound5_SmallPairGraphInputs27_Definitions_002
import Definitions.Def_D1Bound5_SmallPairGraphWitnessData27_Definitions_001
import Definitions.Def_D1Bound5_SmallPairGraphWitnessData27_Definitions_003

section
namespace D1Bound5
set_option maxRecDepth 100000
set_option maxHeartbeats 0

open PairGraphPrepared27

theorem _root_.solution :
    pairClosureIndexedWitnessBool smallPairA_27 smallPairB_27 anchorRoot
      (10^1100) smallPairClosure_27 witnesses destinations = true := by
  decide +kernel



end D1Bound5
end
