-- Prove2me | solution 1 for D1Bound5.firstPairGeometryRow_35_has_fixed_row
-- status  : ACCEPTED   (prove)
-- author  : @tp
-- created : 2026-10-24T05:41:59.663278+00:00
-- url     : https://prove2.me/submissions/4d376236-3ebe-4b1f-8279-e0efa772bd6b

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
import Definitions.Def_D1Bound5_FirstPairGeometryData_Definitions_001
import Definitions.Def_D1Bound5_FirstPairGeometryFixedRows_Definitions
import Definitions.Def_D1Bound5_OneSmallCutoffArithmetic_Definitions_001
import Definitions.Def_D1Bound5_OneSmallCutoffArithmetic_Definitions_002

section
namespace D1Bound5





set_option maxRecDepth 100000
set_option maxHeartbeats 0







































































theorem _root_.solution :
    ∃ r ∈ oneSmallCutoffRows, FirstPairGeometryMatches firstPairGeometryRow_35 r := by
  refine ⟨oneSmallCutoffRow_48,?_,?_⟩
  · decide +kernel
  · decide +kernel













end D1Bound5
end
