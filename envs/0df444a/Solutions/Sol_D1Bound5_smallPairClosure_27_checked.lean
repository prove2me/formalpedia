-- Prove2me | solution 1 for D1Bound5.smallPairClosure_27_checked
-- status  : ACCEPTED   (prove)
-- author  : @tp
-- created : 2026-10-24T02:04:07.507209+00:00
-- url     : https://prove2.me/submissions/d88e1024-0963-4322-953d-dc598990ec91

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
import Definitions.Def_D1Bound5_SmallPairGraphInputs27_Definitions_001
import Definitions.Def_D1Bound5_SmallPairGraphInputs27_Definitions_002
import Definitions.Def_D1Bound5_SmallPairGraphWitnessData27_Definitions_001
import Definitions.Def_D1Bound5_SmallPairGraphWitnessData27_Definitions_003
import Theorems.Thm_D1Bound5_PairGraphPrepared27_indexed_checked
import Theorems.Thm_D1Bound5_pairClosureBool_of_indexed_witness_checked

section
namespace D1Bound5
set_option maxRecDepth 100000
set_option maxHeartbeats 0

open PairGraphPrepared27



theorem _root_.solution :
    pairClosureBool smallPairA_27 smallPairB_27
      (10^1100) smallPairClosure_27 = true :=
  pairClosureBool_of_indexed_witness_checked (by decide) smallPairA_27 smallPairB_27 anchorRoot
    (10^1100) smallPairClosure_27 witnesses destinations PairGraphPrepared27.indexed_checked

end D1Bound5
end
