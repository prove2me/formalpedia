-- Prove2me | solution 1 for D1Bound5.smallTripleFilter_9_checked
-- status  : ACCEPTED   (prove)
-- author  : @tp
-- created : 2026-10-24T04:45:46.254373+00:00
-- url     : https://prove2.me/submissions/8072b540-37c3-4dac-b258-17bb5809b653

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
import Definitions.Def_D1Bound5_SmallTripleExtensionData9_Definitions

section
namespace D1Bound5
open QuadInt
set_option maxRecDepth 32768
set_option maxHeartbeats 8000000













theorem _root_.solution :
    tripleExtensionFilterBool smallTripleAnchorA_9 smallTripleAnchorB_9
      smallTripleAnchorC_9 smallTriplePairClosure_9 smallTripleAllowed_9 = true := by
  decide +kernel



end D1Bound5
end
