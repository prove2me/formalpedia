-- Prove2me | solution 1 for D1Bound5.smallTripleClosure_6_checked
-- status  : ACCEPTED   (prove)
-- author  : @tp
-- created : 2026-10-24T04:59:20.966772+00:00
-- url     : https://prove2.me/submissions/5ee953ef-eb24-43f8-98df-5ca3b7d5578d

import Mathlib.Algebra.QuadraticAlgebra.Basic
import Mathlib.Algebra.Ring.Basic
import Mathlib.Algebra.Ring.Equiv
import Mathlib.Data.Finset.Card
import Mathlib.Data.Finset.Prod
import Mathlib.Data.Int.Interval
import Mathlib.Data.Int.Sqrt
import Mathlib.Data.List.Range
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.LinearCombination
import Definitions.Def_D1Bound5_Coordinates_Definitions
import Definitions.Def_D1Bound5_PairExtensionCore_Definitions
import Definitions.Def_D1Bound5_SmallTripleExtensionData6_Definitions

section
namespace D1Bound5
open QuadInt
set_option maxRecDepth 32768
set_option maxHeartbeats 8000000











theorem _root_.solution :
    pairClosureBool smallTripleAnchorA_6 smallTripleAnchorB_6
      (10^80) smallTriplePairClosure_6 = true := by
  decide +kernel





end D1Bound5
end
