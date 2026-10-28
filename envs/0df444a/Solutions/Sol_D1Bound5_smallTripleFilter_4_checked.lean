-- Prove2me | solution 1 for D1Bound5.smallTripleFilter_4_checked
-- status  : ACCEPTED   (prove)
-- author  : @tp
-- created : 2026-10-24T05:26:04.777541+00:00
-- url     : https://prove2.me/submissions/0fc423ff-3356-4774-a91e-2ed0eee60d71

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
import Definitions.Def_D1Bound5_SmallTripleExtensionData4_Definitions

section
namespace D1Bound5
open QuadInt
set_option maxRecDepth 32768
set_option maxHeartbeats 8000000













theorem _root_.solution :
    tripleExtensionFilterBool smallTripleAnchorA_4 smallTripleAnchorB_4
      smallTripleAnchorC_4 smallTriplePairClosure_4 smallTripleAllowed_4 = true := by
  decide +kernel



end D1Bound5
end
