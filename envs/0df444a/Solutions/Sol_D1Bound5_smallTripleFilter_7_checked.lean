-- Prove2me | solution 1 for D1Bound5.smallTripleFilter_7_checked
-- status  : ACCEPTED   (prove)
-- author  : @tp
-- created : 2026-10-24T05:04:52.769514+00:00
-- url     : https://prove2.me/submissions/3e3788eb-aa90-4eed-af93-8b41ae0ee4da

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
import Definitions.Def_D1Bound5_SmallTripleExtensionData7_Definitions

section
namespace D1Bound5
open QuadInt
set_option maxRecDepth 32768
set_option maxHeartbeats 8000000













theorem _root_.solution :
    tripleExtensionFilterBool smallTripleAnchorA_7 smallTripleAnchorB_7
      smallTripleAnchorC_7 smallTriplePairClosure_7 smallTripleAllowed_7 = true := by
  decide +kernel



end D1Bound5
end
