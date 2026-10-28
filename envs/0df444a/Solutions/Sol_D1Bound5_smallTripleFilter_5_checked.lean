-- Prove2me | solution 1 for D1Bound5.smallTripleFilter_5_checked
-- status  : ACCEPTED   (prove)
-- author  : @tp
-- created : 2026-10-24T04:26:20.363243+00:00
-- url     : https://prove2.me/submissions/d7276361-41c5-42b9-b73b-5d6eefc104b7

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
import Definitions.Def_D1Bound5_SmallTripleExtensionData5_Definitions

section
namespace D1Bound5
open QuadInt
set_option maxRecDepth 32768
set_option maxHeartbeats 8000000













theorem _root_.solution :
    tripleExtensionFilterBool smallTripleAnchorA_5 smallTripleAnchorB_5
      smallTripleAnchorC_5 smallTriplePairClosure_5 smallTripleAllowed_5 = true := by
  decide +kernel



end D1Bound5
end
