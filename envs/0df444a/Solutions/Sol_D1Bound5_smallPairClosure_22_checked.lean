-- Prove2me | solution 1 for D1Bound5.smallPairClosure_22_checked
-- status  : ACCEPTED   (prove)
-- author  : @tp
-- created : 2026-10-24T02:24:26.155227+00:00
-- url     : https://prove2.me/submissions/18c77191-81a2-4f3e-b1b7-623cc7dbedcb

import Mathlib.Algebra.QuadraticAlgebra.Basic
import Mathlib.Algebra.Ring.Basic
import Mathlib.Algebra.Ring.Equiv
import Mathlib.Data.Finset.Card
import Mathlib.Data.Finset.Prod
import Mathlib.Data.Int.Interval
import Mathlib.Data.Int.Sqrt
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.LinearCombination
import Definitions.Def_D1Bound5_Coordinates_Definitions
import Definitions.Def_D1Bound5_PairExtensionCore_Definitions
import Definitions.Def_D1Bound5_SmallPairGraphInputs22_Definitions_001
import Definitions.Def_D1Bound5_SmallPairGraphInputs22_Definitions_002
import Definitions.Def_D1Bound5_SmallPairGraphWitnessData22_Definitions_001
import Definitions.Def_D1Bound5_SmallPairGraphWitnessData22_Definitions_003
import Theorems.Thm_D1Bound5_PairGraphPrepared22_indexed_checked
import Theorems.Thm_D1Bound5_pairClosureBool_of_indexed_witness_checked

section
set_option autoImplicit false

namespace D1Bound5
set_option maxRecDepth 100000
set_option maxHeartbeats 0

open PairGraphPrepared22



theorem _root_.solution :
    pairClosureBool smallPairA_22 smallPairB_22
      (10^1100) smallPairClosure_22 = true :=
  pairClosureBool_of_indexed_witness_checked (by decide) smallPairA_22 smallPairB_22 anchorRoot
    (10^1100) smallPairClosure_22 witnesses destinations PairGraphPrepared22.indexed_checked

end D1Bound5
end
