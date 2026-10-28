-- Prove2me | solution 1 for D1Bound5.smallPairClosure_26_checked
-- status  : ACCEPTED   (prove)
-- author  : @tp
-- created : 2026-10-24T02:17:17.615448+00:00
-- url     : https://prove2.me/submissions/d6d5b3bd-ac3d-4418-a8b4-093dfd8cd635

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
import Definitions.Def_D1Bound5_SmallPairGraphInputs26_Definitions_001
import Definitions.Def_D1Bound5_SmallPairGraphInputs26_Definitions_002
import Definitions.Def_D1Bound5_SmallPairGraphWitnessData26_Definitions_001
import Definitions.Def_D1Bound5_SmallPairGraphWitnessData26_Definitions_003
import Theorems.Thm_D1Bound5_PairGraphPrepared26_indexed_checked
import Theorems.Thm_D1Bound5_pairClosureBool_of_indexed_witness_checked

section
namespace D1Bound5
set_option maxRecDepth 100000
set_option maxHeartbeats 0

open PairGraphPrepared26



theorem _root_.solution :
    pairClosureBool smallPairA_26 smallPairB_26
      (10^1100) smallPairClosure_26 = true :=
  pairClosureBool_of_indexed_witness_checked (by decide) smallPairA_26 smallPairB_26 anchorRoot
    (10^1100) smallPairClosure_26 witnesses destinations PairGraphPrepared26.indexed_checked

end D1Bound5
end
