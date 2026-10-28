-- Prove2me | solution 1 for D1Bound5.smallTripleFilter_10_checked
-- status  : ACCEPTED   (prove)
-- author  : @tp
-- created : 2026-10-24T05:51:19.292651+00:00
-- url     : https://prove2.me/submissions/0aab81c0-f9a6-44cb-8e95-77bcdd93048a

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
import Definitions.Def_D1Bound5_SmallTripleExtensionData10_Definitions

section
namespace D1Bound5
open QuadInt
set_option maxRecDepth 32768
set_option maxHeartbeats 8000000













theorem _root_.solution :
    tripleExtensionFilterBool smallTripleAnchorA_10 smallTripleAnchorB_10
      smallTripleAnchorC_10 smallTriplePairClosure_10 smallTripleAllowed_10 = true := by
  decide +kernel



end D1Bound5
end
