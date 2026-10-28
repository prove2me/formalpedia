-- Prove2me | solution 1 for D1Bound5.firstPairGeometryRow_34_has_fixed_row
-- status  : ACCEPTED   (prove)
-- author  : @tp
-- created : 2026-10-24T04:55:00.678758+00:00
-- url     : https://prove2.me/submissions/3fb27991-fda5-4dca-98b2-cf05f9677f0b

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
    ∃ r ∈ oneSmallCutoffRows, FirstPairGeometryMatches firstPairGeometryRow_34 r := by
  refine ⟨oneSmallCutoffRow_47,?_,?_⟩
  · decide +kernel
  · decide +kernel















end D1Bound5
end
