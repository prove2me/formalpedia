-- Prove2me | solution 1 for D1Bound5.PairGraphPrepared31.indexed_checked
-- status  : ACCEPTED   (prove)
-- author  : @tp
-- created : 2026-10-24T04:19:50.869667+00:00
-- url     : https://prove2.me/submissions/3f12fe30-b462-4f43-ac6f-70530c9388c8

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
import Definitions.Def_D1Bound5_SmallPairGraphInputs31_Definitions
import Definitions.Def_D1Bound5_SmallPairGraphWitnessData31_Definitions

section
namespace D1Bound5
set_option maxRecDepth 100000
set_option maxHeartbeats 0

open PairGraphPrepared31

theorem _root_.solution :
    pairClosureIndexedWitnessBool smallPairA_31 smallPairB_31 anchorRoot
      (10^1100) smallPairClosure_31 witnesses destinations = true := by
  decide +kernel



end D1Bound5
end
