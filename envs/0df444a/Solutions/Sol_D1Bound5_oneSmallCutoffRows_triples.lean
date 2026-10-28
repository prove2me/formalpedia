-- Prove2me | solution 1 for D1Bound5.oneSmallCutoffRows_triples
-- status  : ACCEPTED   (prove)
-- author  : @tp
-- created : 2026-10-24T04:21:51.314964+00:00
-- url     : https://prove2.me/submissions/a577b13b-3c4c-4b7d-ba3a-e1a6ed4be132

import Mathlib.Algebra.QuadraticAlgebra.Basic
import Mathlib.Algebra.Ring.Basic
import Mathlib.Algebra.Ring.Equiv
import Mathlib.Data.Finset.Card
import Mathlib.Data.Finset.Prod
import Mathlib.Data.Int.Interval
import Mathlib.Data.Int.Sqrt
import Mathlib.Data.List.Range
import Mathlib.Tactic.IntervalCases
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.LinearCombination
import Definitions.Def_D1Bound5_Coordinates_Definitions
import Definitions.Def_D1Bound5_OneSmallCutoffArithmetic_Definitions_001
import Definitions.Def_D1Bound5_OneSmallCutoffArithmetic_Definitions_002
import Definitions.Def_D1Bound5_OneSmallRows_Definitions

section
namespace D1Bound5
open QuadInt



namespace OneSmallCutoffRow



























end OneSmallCutoffRow

set_option maxRecDepth 100000
set_option maxHeartbeats 0









































































































































































































































/-- The arithmetic rows cover exactly the 56 finite-table triples and
the separate rational triple (1,3,8), with their printed cutoffs. -/
theorem _root_.solution :
    (oneSmallCutoffRows.map OneSmallCutoffRow.triple).toFinset =
      insert (⟨0,1,(1,0),(3,0),(8,0),1024⟩ : OneSmallTripleRow)
        oneSmallFixedRows := by
  decide +kernel



end D1Bound5
end
