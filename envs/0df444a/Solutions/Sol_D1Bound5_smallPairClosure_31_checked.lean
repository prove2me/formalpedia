-- Prove2me | solution 1 for D1Bound5.smallPairClosure_31_checked
-- status  : ACCEPTED   (prove)
-- author  : @tp
-- created : 2026-10-24T02:04:08.495782+00:00
-- url     : https://prove2.me/submissions/0e4f4581-caec-409e-9835-018f0b582056

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
import Definitions.Def_D1Bound5_SmallPairGraphInputs31_Definitions
import Definitions.Def_D1Bound5_SmallPairGraphWitnessData31_Definitions
import Theorems.Thm_D1Bound5_PairGraphPrepared31_indexed_checked
import Theorems.Thm_D1Bound5_pairClosureBool_of_indexed_witness_checked

section
namespace D1Bound5
set_option maxRecDepth 100000
set_option maxHeartbeats 0

open PairGraphPrepared31



theorem _root_.solution :
    pairClosureBool smallPairA_31 smallPairB_31
      (10^1100) smallPairClosure_31 = true :=
  pairClosureBool_of_indexed_witness_checked (by decide) smallPairA_31 smallPairB_31 anchorRoot
    (10^1100) smallPairClosure_31 witnesses destinations PairGraphPrepared31.indexed_checked

end D1Bound5
end
