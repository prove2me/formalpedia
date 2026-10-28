-- Prove2me | solution 1 for D1Bound5.firstPairGeometryRow_5_has_fixed_row
-- status  : ACCEPTED   (prove)
-- author  : @tp
-- created : 2026-10-24T05:39:44.681749+00:00
-- url     : https://prove2.me/submissions/ceed6884-bf93-4f66-a7a5-e14e0ee05934

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
    ∃ r ∈ oneSmallCutoffRows, FirstPairGeometryMatches firstPairGeometryRow_5 r := by
  refine ⟨oneSmallCutoffRow_9,?_,?_⟩
  · decide +kernel
  · decide +kernel









































































end D1Bound5
end
