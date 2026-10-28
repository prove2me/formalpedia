-- Prove2me | solution 1 for D1Bound5.smallPairClosure_32_checked
-- status  : ACCEPTED   (prove)
-- author  : @tp
-- created : 2026-10-24T02:04:05.915105+00:00
-- url     : https://prove2.me/submissions/610a4640-1a02-4f07-90d9-04e9a788ddef

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
import Definitions.Def_D1Bound5_SmallPairGraphInputs32_Definitions
import Definitions.Def_D1Bound5_SmallPairGraphWitnessData32_Definitions
import Theorems.Thm_D1Bound5_PairGraphPrepared32_indexed_checked
import Theorems.Thm_D1Bound5_pairClosureBool_of_indexed_witness_checked

section
namespace D1Bound5
set_option maxRecDepth 100000
set_option maxHeartbeats 0

open PairGraphPrepared32



theorem _root_.solution :
    pairClosureBool smallPairA_32 smallPairB_32
      (10^1100) smallPairClosure_32 = true :=
  pairClosureBool_of_indexed_witness_checked (by decide) smallPairA_32 smallPairB_32 anchorRoot
    (10^1100) smallPairClosure_32 witnesses destinations PairGraphPrepared32.indexed_checked

end D1Bound5
end
