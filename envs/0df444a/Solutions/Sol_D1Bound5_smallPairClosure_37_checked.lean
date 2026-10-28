-- Prove2me | solution 1 for D1Bound5.smallPairClosure_37_checked
-- status  : ACCEPTED   (prove)
-- author  : @tp
-- created : 2026-10-24T02:13:01.021659+00:00
-- url     : https://prove2.me/submissions/b219be2f-5944-4a7d-869d-acdf72abb478

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
import Definitions.Def_D1Bound5_SmallPairGraphInputs37_Definitions_001
import Definitions.Def_D1Bound5_SmallPairGraphInputs37_Definitions_002
import Definitions.Def_D1Bound5_SmallPairGraphWitnessData37_Definitions_001
import Definitions.Def_D1Bound5_SmallPairGraphWitnessData37_Definitions_003
import Theorems.Thm_D1Bound5_PairGraphPrepared37_indexed_checked
import Theorems.Thm_D1Bound5_pairClosureBool_of_indexed_witness_checked

section
set_option autoImplicit false

namespace D1Bound5
set_option maxRecDepth 100000
set_option maxHeartbeats 0

open PairGraphPrepared37



theorem _root_.solution :
    pairClosureBool smallPairA_37 smallPairB_37
      (10^1100) smallPairClosure_37 = true :=
  pairClosureBool_of_indexed_witness_checked (by decide) smallPairA_37 smallPairB_37 anchorRoot
    (10^1100) smallPairClosure_37 witnesses destinations PairGraphPrepared37.indexed_checked

end D1Bound5
end
