-- Prove2me | solution 1 for D1Bound5.FirstPairGeometryMatches.residual_rates
-- status  : ACCEPTED   (prove)
-- author  : @tp
-- created : 2026-10-23T23:48:41.901926+00:00
-- url     : https://prove2.me/submissions/d4839aaa-f81f-4907-b7e5-2ca03b12c3b9

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
import Theorems.Thm_D1Bound5_FirstPairGeometryMatches_pair_invariants

section
namespace D1Bound5



/-- The pair-dependent residual coefficients agree exactly. The P rate
uses a different geometric enclosure and is deliberately not identified. -/
theorem _root_.solution
    (g : FirstPairGeometryRow) (r : OneSmallCutoffRow)
    (h : FirstPairGeometryMatches g r) :
    g.R2 = r.R2 ∧ g.Rn = r.Rn ∧ g.R3 = r.R3 ∧
      g.R4 = r.R4 ∧ g.R5 = r.R5 := by
  obtain ⟨_,hb,hd⟩ := FirstPairGeometryMatches.pair_invariants g r h
  simp [FirstPairGeometryRow.R2,FirstPairGeometryRow.Rn,
    FirstPairGeometryRow.R3,FirstPairGeometryRow.R4,FirstPairGeometryRow.R5,
    OneSmallCutoffRow.R2,OneSmallCutoffRow.Rn,
    OneSmallCutoffRow.R3,OneSmallCutoffRow.R4,OneSmallCutoffRow.R5,hb,hd]

end D1Bound5
end
